-- Prove2me | solution 1 for CritWinSpin.p3b_fp_scale
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-15T23:54:40.808757+00:00
-- url     : https://prove2.me/submissions/dcec0711-217f-4af3-bb3c-dbbac4dc8143

import Mathlib
import Definitions.Def_CritWinSpin_SpinLaw
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
open scoped BigOperators Nat

namespace CritWinSpin

noncomputable def P3bF_Z (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))

noncomputable def P3bF_Z1 (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))

noncomputable def P3bF_Z2 (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))

lemma P3bF_Z_pos (S : SpinLaw) (t : ℝ) : 0 < P3bF_Z S t := by
  unfold P3bF_Z
  apply Finset.sum_pos'
  · intro x hx
    exact mul_nonneg (by exact_mod_cast (le_of_lt (S.pos x hx))) (Real.exp_pos _).le
  · refine ⟨1, S.one_mem, ?_⟩
    exact mul_pos (by exact_mod_cast S.pos 1 S.one_mem) (Real.exp_pos _)

lemma P3bF_Z_zero (S : SpinLaw) : P3bF_Z S 0 = 1 := by
  unfold P3bF_Z
  simp only [zero_mul, Real.exp_zero, mul_one]
  exact_mod_cast S.sum_one

lemma P3bF_variance_pos (S : SpinLaw) : 0 < variance S := by
  have hvQ : 0 < varQ S := by
    have h1 : 0 < (1 : ℚ) ^ 2 * S.ρ 1 := by simpa using S.pos 1 S.one_mem
    have hnonneg : ∀ x ∈ S.A, 0 ≤ x ^ 2 * S.ρ x := fun x hx =>
      mul_nonneg (sq_nonneg x) (S.pos x hx).le
    have hle : (1 : ℚ) ^ 2 * S.ρ 1 ≤ varQ S := by
      rw [varQ]
      exact Finset.single_le_sum hnonneg S.one_mem
    exact lt_of_lt_of_le h1 hle
  exact Rat.cast_pos.mpr hvQ

lemma P3bF_tau_mul_variance (S : SpinLaw) : tau S * variance S = 1 := by
  have hvpos : 0 < variance S := P3bF_variance_pos S
  have hvne : variance S ≠ 0 := ne_of_gt hvpos
  have htau : tau S = 1 / variance S := by
    unfold tau tauQ variance
    push_cast
    rfl
  rw [htau]
  field_simp [hvne]

lemma P3bF_tau_pos (S : SpinLaw) : 0 < tau S := by
  have h1 := P3bF_tau_mul_variance S
  have hv := P3bF_variance_pos S
  nlinarith

lemma P3bF_Z1_zero (S : SpinLaw) : P3bF_Z1 S 0 = 0 := by
  unfold P3bF_Z1
  simp only [zero_mul, Real.exp_zero, mul_one]
  have hneg : (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ)) =
      ∑ x ∈ S.A, -((S.ρ x : ℝ) * (x : ℝ)) := by
    refine Finset.sum_bij (fun x _ => -x) ?_ ?_ ?_ ?_
    · intro x hx; exact S.neg_mem x hx
    · intro a _ b _ hab; simpa using congrArg Neg.neg hab
    · intro b hb; exact ⟨-b, S.neg_mem b hb, by simp⟩
    · intro x hx
      rw [S.symm x hx, Rat.cast_neg]
      ring
  rw [Finset.sum_neg_distrib] at hneg
  linarith

lemma P3bF_Z2_zero (S : SpinLaw) : P3bF_Z2 S 0 = variance S := by
  unfold P3bF_Z2 variance varQ
  simp only [zero_mul, Real.exp_zero, mul_one]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma P3bF_hasDerivAt_Z (S : SpinLaw) (t : ℝ) : HasDerivAt (P3bF_Z S) (P3bF_Z1 S t) t := by
  unfold P3bF_Z P3bF_Z1
  convert HasDerivAt.fun_sum (u := S.A) (A := fun x s => (S.ρ x : ℝ) * Real.exp (s * (x : ℝ)))
      (A' := fun x => (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) (x := t) (fun x _ => ?_)
  have hmul : HasDerivAt (fun s : ℝ => s * (x : ℝ)) (x : ℝ) t := by
    simpa using (hasDerivAt_id t).mul_const (x : ℝ)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (s * (x : ℝ))) (Real.exp (t * (x : ℝ)) * (x : ℝ)) t :=
    hmul.exp
  have hd := hexp.const_mul (S.ρ x : ℝ)
  rw [show (S.ρ x : ℝ) * (Real.exp (t * (x : ℝ)) * (x : ℝ)) =
      (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ)) from by ring] at hd
  exact hd

lemma P3bF_hasDerivAt_Z1 (S : SpinLaw) (t : ℝ) : HasDerivAt (P3bF_Z1 S) (P3bF_Z2 S t) t := by
  unfold P3bF_Z1 P3bF_Z2
  convert HasDerivAt.fun_sum (u := S.A)
      (A := fun x s => (S.ρ x : ℝ) * (x : ℝ) * Real.exp (s * (x : ℝ)))
      (A' := fun x => (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))) (x := t) (fun x _ => ?_)
  have hmul : HasDerivAt (fun s : ℝ => s * (x : ℝ)) (x : ℝ) t := by
    simpa using (hasDerivAt_id t).mul_const (x : ℝ)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (s * (x : ℝ))) (Real.exp (t * (x : ℝ)) * (x : ℝ)) t :=
    hmul.exp
  have hd := hexp.const_mul ((S.ρ x : ℝ) * (x : ℝ))
  rw [show (S.ρ x : ℝ) * (x : ℝ) * (Real.exp (t * (x : ℝ)) * (x : ℝ)) =
      (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ)) from by ring] at hd
  exact hd

lemma P3bF_hasDerivAt_phi (S : SpinLaw) (t : ℝ) :
    HasDerivAt (phi S) (P3bF_Z1 S t / P3bF_Z S t) t := by
  change HasDerivAt (fun s => Real.log (P3bF_Z S s)) (P3bF_Z1 S t / P3bF_Z S t) t
  exact (P3bF_hasDerivAt_Z S t).log (ne_of_gt (P3bF_Z_pos S t))

lemma P3bF_deriv_phi (S : SpinLaw) : deriv (phi S) = fun t => P3bF_Z1 S t / P3bF_Z S t := by
  funext t
  exact (P3bF_hasDerivAt_phi S t).deriv

lemma P3bF_phi_analyticOnNhd (S : SpinLaw) : AnalyticOnNhd ℝ (phi S) Set.univ := by
  intro t _
  change AnalyticAt ℝ (fun s => Real.log (P3bF_Z S s)) t
  have hZ : AnalyticAt ℝ (P3bF_Z S) t := by
    unfold P3bF_Z
    refine Finset.analyticAt_fun_sum S.A fun x _ => ?_
    exact analyticAt_const.mul (analyticAt_rexp.comp ((analyticAt_id : AnalyticAt ℝ id t).mul analyticAt_const))
  exact (analyticAt_log (P3bF_Z_pos S t)).comp hZ

lemma P3bF_phi_contDiff (S : SpinLaw) : ContDiff ℝ ⊤ (phi S) :=
  (P3bF_phi_analyticOnNhd S).contDiff

lemma P3bF_iteratedDeriv_one_zero (S : SpinLaw) : iteratedDeriv 1 (phi S) 0 = 0 := by
  rw [iteratedDeriv_one, P3bF_deriv_phi]
  dsimp only
  rw [P3bF_Z1_zero, P3bF_Z_zero]
  norm_num

lemma P3bF_iteratedDeriv_two_zero (S : SpinLaw) : iteratedDeriv 2 (phi S) 0 = variance S := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, P3bF_deriv_phi]
  have hd := (P3bF_hasDerivAt_Z1 S 0).div (P3bF_hasDerivAt_Z S 0) (ne_of_gt (P3bF_Z_pos S 0))
  change HasDerivAt (fun t => P3bF_Z1 S t / P3bF_Z S t) _ 0 at hd
  rw [hd.deriv, P3bF_Z2_zero, P3bF_Z_zero, P3bF_Z1_zero]
  norm_num

lemma P3bF_phi_even (S : SpinLaw) (t : ℝ) : phi S (-t) = phi S t := by
  unfold phi
  have hsum :
      (∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp ((-t) * (x : ℝ))) =
      (∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) := by
    classical
    refine Finset.sum_bij (fun x _ => -x) ?_ ?_ ?_ ?_
    · intro x hx; exact S.neg_mem x hx
    · intro a _ b _ h; simpa using congrArg Neg.neg h
    · intro b hb; exact ⟨-b, S.neg_mem b hb, by simp⟩
    · intro x hx
      rw [S.symm x hx, Rat.cast_neg]
      congr 2
      ring
  rw [hsum]

lemma P3bF_iteratedDeriv_even_symm (S : SpinLaw) (n : ℕ) :
    ∀ t : ℝ, iteratedDeriv n (phi S) (-t) = (-1 : ℝ) ^ n * iteratedDeriv n (phi S) t := by
  induction n with
  | zero => intro t; simp [P3bF_phi_even S t]
  | succ n ih =>
    intro t
    have hdiff : Differentiable ℝ (iteratedDeriv n (phi S)) :=
      (P3bF_phi_contDiff S).differentiable_iteratedDeriv n
        (by exact_mod_cast (WithTop.coe_lt_top (n : ℕ∞) : ((n : ℕ∞) : WithTop ℕ∞) < ⊤))
    have hleft : HasDerivAt (fun s => iteratedDeriv n (phi S) (-s))
        (-iteratedDeriv (n + 1) (phi S) (-t)) t := by
      have h1 : HasDerivAt (iteratedDeriv n (phi S)) (iteratedDeriv (n + 1) (phi S) (-t)) (-t) := by
        rw [iteratedDeriv_succ]
        exact (hdiff (-t)).hasDerivAt
      have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
      have h2 : HasDerivAt (fun s => iteratedDeriv n (phi S) (-s))
          (iteratedDeriv (n + 1) (phi S) (-t) * (-1)) t := h1.comp t hneg
      rw [mul_neg_one] at h2
      exact h2
    have hright : HasDerivAt (fun s => (-1 : ℝ) ^ n * iteratedDeriv n (phi S) s)
        ((-1 : ℝ) ^ n * iteratedDeriv (n + 1) (phi S) t) t := by
      rw [iteratedDeriv_succ]
      exact (hdiff t).hasDerivAt.const_mul ((-1 : ℝ) ^ n)
    have heqFun : (fun s => iteratedDeriv n (phi S) (-s)) =
        (fun s => (-1 : ℝ) ^ n * iteratedDeriv n (phi S) s) := funext ih
    rw [heqFun] at hleft
    have hderivEq := hleft.unique hright
    calc
      iteratedDeriv (n + 1) (phi S) (-t) = -(-iteratedDeriv (n + 1) (phi S) (-t)) := by ring
      _ = -((-1 : ℝ) ^ n * iteratedDeriv (n + 1) (phi S) t) := by rw [hderivEq]
      _ = (-1 : ℝ) ^ (n + 1) * iteratedDeriv (n + 1) (phi S) t := by rw [pow_succ]; ring

lemma P3bF_iteratedDeriv_odd_zero (S : SpinLaw) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (phi S) 0 = 0 := by
  have h := P3bF_iteratedDeriv_even_symm S (2 * k + 1) 0
  simp only [neg_zero] at h
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
  rw [hpow] at h
  linarith

lemma P3bF_iteratedDeriv_add (m k : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv m (iteratedDeriv k f) = iteratedDeriv (m + k) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add_apply]

lemma P3bF_contDiff_iteratedDeriv (k : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv k f) := by
  apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
  intro m _
  rw [P3bF_iteratedDeriv_add]
  exact hf.differentiable_iteratedDeriv (m + k)
    (by exact_mod_cast (WithTop.coe_lt_top ((m + k : ℕ) : ℕ∞) : (((m + k : ℕ) : ℕ∞) : WithTop ℕ∞) < ⊤))

lemma P3bF_nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [← WithTop.coe_natCast]
  exact WithTop.coe_le_coe.mpr le_top

lemma P3bF_nat_add_one_le_infty (n : ℕ) :
    ((n : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [show ((n : WithTop ℕ∞) + 1) = ((n + 1 : ℕ) : WithTop ℕ∞) by norm_cast]
  exact P3bF_nat_le_infty (n + 1)

lemma P3bF_taylor_bound_Icc (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |t| ≤ 1 →
      |f t - ∑ k ∈ Finset.range (n + 1), (iteratedDeriv k f 0 / (k ! : ℝ)) * t ^ k| ≤
        M * |t| ^ (n + 1) := by
  have hcont : ContinuousOn (fun x => ‖iteratedDeriv (n + 1) f x‖) (Set.Icc (-1 : ℝ) 1) :=
    (hf.continuous_iteratedDeriv (n + 1)
      (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))).norm.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let M : ℝ := max 0 B / ((n + 1)! : ℝ)
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M, hM0, fun t ht => ?_⟩
  by_cases ht0 : t = 0
  · subst ht0
    simp [Finset.sum_range_succ']
  · have htne : (0 : ℝ) ≠ t := Ne.symm ht0
    have hfC : ContDiffOn ℝ (n + 1) f (Set.uIcc 0 t) :=
      (hf.of_le (P3bF_nat_add_one_le_infty n)).contDiffOn
    obtain ⟨x', hx'mem, hx'eq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv htne hfC
    have hu : UniqueDiffOn ℝ (Set.uIcc 0 t) := uniqueDiffOn_uIcc htne
    have htay : taylorWithinEval f n (Set.uIcc 0 t) 0 t =
        ∑ k ∈ Finset.range (n + 1), (iteratedDeriv k f 0 / (k ! : ℝ)) * t ^ k := by
      rw [taylor_within_apply]
      apply Finset.sum_congr rfl
      intro k _
      have hwithin : iteratedDerivWithin k f (Set.uIcc 0 t) 0 = iteratedDeriv k f 0 :=
        iteratedDerivWithin_eq_iteratedDeriv hu
          (hf.of_le (P3bF_nat_le_infty k)).contDiffAt Set.left_mem_uIcc
      rw [hwithin, smul_eq_mul, sub_zero]
      ring
    rw [htay, sub_zero] at hx'eq
    have hx'Icc : x' ∈ Set.Icc (-1 : ℝ) 1 := by
      have hx'uIcc : x' ∈ Set.uIcc 0 t := Set.uIoo_subset_uIcc_self hx'mem
      have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
      have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp ht
      exact Set.uIcc_subset_Icc h0 htIcc hx'uIcc
    have hBx' : |iteratedDeriv (n + 1) f x'| ≤ max 0 B := by
      have h1 := hB x' hx'Icc
      rw [Real.norm_eq_abs] at h1
      have h2 : |iteratedDeriv (n + 1) f x'| = ‖|iteratedDeriv (n + 1) f x'|‖ :=
        (abs_abs _).symm
      rw [h2]
      exact h1.trans (le_max_right 0 B)
    rw [hx'eq, abs_div, abs_mul, abs_pow, Nat.abs_cast]
    have hfact : (0 : ℝ) < ((n + 1)! : ℝ) := by positivity
    calc
      |iteratedDeriv (n + 1) f x'| * |t| ^ (n + 1) / ((n + 1)! : ℝ)
          ≤ max 0 B * |t| ^ (n + 1) / ((n + 1)! : ℝ) := by gcongr
      _ = M * |t| ^ (n + 1) := by dsimp [M]; ring

lemma P3bF_deriv_phi_div_strictAnti (S : SpinLaw) (hS : IsGHS S) (p : ℕ) (hp : IsTypeP S p) :
    ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ < t₂ → deriv (phi S) t₂ / t₂ < deriv (phi S) t₁ / t₁ := by
  have hp2 : 2 ≤ p := hp.1
  have hpmin : ∀ j : ℕ, 2 ≤ j → j < p → iteratedDeriv (2 * j) (phi S) 0 = 0 := hp.2.1
  have hpneg : iteratedDeriv (2 * p) (phi S) 0 < 0 := hp.2.2
  have hd2_anti : AntitoneOn (iteratedDeriv 2 (phi S)) (Set.Ici 0) := by
    have hd2_diff : Differentiable ℝ (iteratedDeriv 2 (phi S)) :=
      (P3bF_phi_contDiff S).differentiable_iteratedDeriv 2
        (by exact_mod_cast (WithTop.coe_lt_top (2 : ℕ∞) : ((2 : ℕ∞) : WithTop ℕ∞) < ⊤))
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact hd2_diff.continuous.continuousOn
    · exact hd2_diff.differentiableOn
    · intro t ht
      rw [← iteratedDeriv_succ]
      exact hS t (interior_Ici.subset ht).le
  have hneg3 : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → iteratedDeriv 3 (phi S) t < 0 := by
    let f : ℝ → ℝ := iteratedDeriv 3 (phi S)
    have hf_cd : ContDiff ℝ (⊤ : ℕ∞) f :=
      P3bF_contDiff_iteratedDeriv 3 (P3bF_phi_contDiff S)
    let m : ℕ := 2 * p - 4
    have hm1 : m + 1 = 2 * p - 3 := by dsimp [m]; omega
    have hcont : Continuous (iteratedDeriv (m + 1) f) := by
      rw [hm1]
      exact hf_cd.continuous_iteratedDeriv (2 * p - 3) (P3bF_nat_le_infty (2 * p - 3))
    have hderiv0 : iteratedDeriv (m + 1) f 0 < 0 := by
      dsimp [f]
      rw [hm1, P3bF_iteratedDeriv_add, show (2 * p - 3) + 3 = 2 * p by omega]
      exact hpneg
    have hnhds : ∀ᶠ x in nhds (0 : ℝ), iteratedDeriv (m + 1) f x < 0 :=
      hcont.continuousAt.eventually (Iio_mem_nhds hderiv0)
    obtain ⟨δ, hδpos, hδball⟩ := Metric.eventually_nhds_iff.mp hnhds
    refine ⟨δ, hδpos, fun t ht0 htδ => ?_⟩
    have htne : (0 : ℝ) ≠ t := ne_of_lt ht0
    have hfC : ContDiffOn ℝ (m + 1) f (Set.uIcc 0 t) :=
      (hf_cd.of_le (P3bF_nat_add_one_le_infty m)).contDiffOn
    obtain ⟨x', hx'mem, hx'eq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv htne hfC
    have htay0 : taylorWithinEval f m (Set.uIcc 0 t) 0 t = 0 := by
      rw [taylor_within_apply]
      apply Finset.sum_eq_zero
      intro k hk
      have hlt : k + 3 < 2 * p := by
        have := Finset.mem_range.mp hk
        dsimp [m] at this
        omega
      have hu : UniqueDiffOn ℝ (Set.uIcc 0 t) := uniqueDiffOn_uIcc htne
      have hwithin : iteratedDerivWithin k f (Set.uIcc 0 t) 0 = iteratedDeriv k f 0 :=
        iteratedDerivWithin_eq_iteratedDeriv hu
          (hf_cd.of_le (P3bF_nat_le_infty k)).contDiffAt Set.left_mem_uIcc
      have hk0 : iteratedDeriv k f 0 = 0 := by
        dsimp [f]
        rw [P3bF_iteratedDeriv_add]
        rcases Nat.even_or_odd (k + 3) with ⟨j, hj⟩ | ⟨j, hj⟩
        · have hj2 : 2 ≤ j := by omega
          have hjp : j < p := by omega
          rw [show k + 3 = 2 * j by omega]
          exact hpmin j hj2 hjp
        · rw [hj]
          exact P3bF_iteratedDeriv_odd_zero S j
      rw [hwithin, hk0, smul_zero]
    rw [htay0, sub_zero, sub_zero] at hx'eq
    have hx'Ioo : x' ∈ Set.Ioo 0 t := by simpa [Set.uIoo_of_lt ht0] using hx'mem
    have hx'dist : dist x' 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx'Ioo.1]
      exact hx'Ioo.2.trans htδ
    have hneg_x' : iteratedDeriv (m + 1) f x' < 0 := hδball hx'dist
    change f t < 0
    rw [hx'eq]
    have hpow : 0 < t ^ (m + 1) := pow_pos ht0 (m + 1)
    have hfact : (0 : ℝ) < ((m + 1)! : ℝ) := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg_x' hpow) hfact
  obtain ⟨δ, hδpos, hδneg⟩ := hneg3
  have hd2_lt : ∀ a b : ℝ, 0 ≤ a → a < δ → a < b →
      iteratedDeriv 2 (phi S) b < iteratedDeriv 2 (phi S) a := by
    intro a b ha0 haδ hab
    let b' : ℝ := min b ((a + δ) / 2)
    have hab' : a < b' := lt_min hab (by linarith)
    have hb'le : b' ≤ b := min_le_left _ _
    have hb'δ : b' < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hd2_cd : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv 2 (phi S)) :=
      P3bF_contDiff_iteratedDeriv 2 (P3bF_phi_contDiff S)
    have hd2_diff : Differentiable ℝ (iteratedDeriv 2 (phi S)) :=
      hd2_cd.differentiable (by simp)
    have hstrict : StrictAntiOn (iteratedDeriv 2 (phi S)) (Set.Icc a b') := by
      apply strictAntiOn_of_deriv_neg (convex_Icc a b')
      · exact hd2_diff.continuous.continuousOn
      · intro x hx
        have hx' : x ∈ Set.Ioo a b' := by simpa [interior_Icc] using hx
        rw [← iteratedDeriv_succ]
        exact hδneg x (lt_of_le_of_lt ha0 hx'.1) (hx'.2.trans hb'δ)
    have hlt1 : iteratedDeriv 2 (phi S) b' < iteratedDeriv 2 (phi S) a :=
      hstrict (Set.left_mem_Icc.mpr hab'.le) (Set.right_mem_Icc.mpr hab'.le) hab'
    have hle2 : iteratedDeriv 2 (phi S) b ≤ iteratedDeriv 2 (phi S) b' :=
      hd2_anti (Set.mem_Ici.mpr (le_trans ha0 hab'.le)) (Set.mem_Ici.mpr (le_trans ha0 hab.le)) hb'le
    exact lt_of_le_of_lt hle2 hlt1
  intro t₁ t₂ ht₁pos ht₁₂
  let m₀ : ℝ := min (t₁ / 2) (δ / 2)
  have hm₀pos : 0 < m₀ := lt_min (by linarith) (by linarith)
  have hm₀lt1 : m₀ < t₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hm₀ltδ : m₀ < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hd1_diff : Differentiable ℝ (deriv (phi S)) := by
    rw [← iteratedDeriv_one]
    exact (P3bF_phi_contDiff S).differentiable_iteratedDeriv 1
      (by exact_mod_cast (WithTop.coe_lt_top (1 : ℕ∞) : ((1 : ℕ∞) : WithTop ℕ∞) < ⊤))
  have hd1_has : ∀ x : ℝ, HasDerivAt (deriv (phi S)) (iteratedDeriv 2 (phi S) x) x := by
    intro x
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (hd1_diff x).hasDerivAt
  obtain ⟨d₁, hd₁mem, hd₁eq⟩ := exists_hasDerivAt_eq_slope (deriv (phi S)) (iteratedDeriv 2 (phi S))
    hm₀pos hd1_diff.continuous.continuousOn (fun x _ => hd1_has x)
  obtain ⟨d₂, hd₂mem, hd₂eq⟩ := exists_hasDerivAt_eq_slope (deriv (phi S)) (iteratedDeriv 2 (phi S))
    hm₀lt1 hd1_diff.continuous.continuousOn (fun x _ => hd1_has x)
  obtain ⟨c₂, hc₂mem, hc₂eq⟩ := exists_hasDerivAt_eq_slope (deriv (phi S)) (iteratedDeriv 2 (phi S))
    ht₁₂ hd1_diff.continuous.continuousOn (fun x _ => hd1_has x)
  have hd₁0 : deriv (phi S) 0 = 0 := by
    rw [← iteratedDeriv_one]
    exact P3bF_iteratedDeriv_one_zero S
  have hψm₀ : deriv (phi S) m₀ = m₀ * iteratedDeriv 2 (phi S) d₁ := by
    have h1 := hd₁eq
    rw [hd₁0, sub_zero, sub_zero] at h1
    rw [h1, mul_div_cancel₀ _ (ne_of_gt hm₀pos)]
  have hψ1_sub : deriv (phi S) t₁ - deriv (phi S) m₀ = (t₁ - m₀) * iteratedDeriv 2 (phi S) d₂ := by
    rw [hd₂eq, mul_div_cancel₀ _ (by linarith)]
  have hψ2_sub : deriv (phi S) t₂ - deriv (phi S) t₁ = (t₂ - t₁) * iteratedDeriv 2 (phi S) c₂ := by
    rw [hc₂eq, mul_div_cancel₀ _ (by linarith)]
  have hc₂_le_d₂ : iteratedDeriv 2 (phi S) c₂ ≤ iteratedDeriv 2 (phi S) d₂ :=
    hd2_anti (Set.mem_Ici.mpr (le_trans hm₀pos.le hd₂mem.1.le))
      (Set.mem_Ici.mpr (le_trans ht₁pos.le hc₂mem.1.le)) (le_trans hd₂mem.2.le hc₂mem.1.le)
  have hd₂_lt_d₁ : iteratedDeriv 2 (phi S) d₂ < iteratedDeriv 2 (phi S) d₁ :=
    hd2_lt d₁ d₂ hd₁mem.1.le (hd₁mem.2.trans hm₀ltδ) (lt_trans hd₁mem.2 hd₂mem.1)
  have hc₂_lt_d₁ : iteratedDeriv 2 (phi S) c₂ < iteratedDeriv 2 (phi S) d₁ :=
    lt_of_le_of_lt hc₂_le_d₂ hd₂_lt_d₁
  have hψt₁_gt : t₁ * iteratedDeriv 2 (phi S) c₂ < deriv (phi S) t₁ := by
    have h1 : m₀ * iteratedDeriv 2 (phi S) c₂ < m₀ * iteratedDeriv 2 (phi S) d₁ :=
      mul_lt_mul_of_pos_left hc₂_lt_d₁ hm₀pos
    have h2 : (t₁ - m₀) * iteratedDeriv 2 (phi S) c₂ ≤ (t₁ - m₀) * iteratedDeriv 2 (phi S) d₂ :=
      mul_le_mul_of_nonneg_left hc₂_le_d₂ (by linarith)
    linarith
  have hcross : t₁ * deriv (phi S) t₂ < t₂ * deriv (phi S) t₁ := by
    have hdiff_lt : t₁ * (deriv (phi S) t₂ - deriv (phi S) t₁) < (t₂ - t₁) * deriv (phi S) t₁ := by
      have hmul : t₁ * ((t₂ - t₁) * iteratedDeriv 2 (phi S) c₂) =
          (t₂ - t₁) * (t₁ * iteratedDeriv 2 (phi S) c₂) := by ring
      rw [hψ2_sub, hmul]
      exact mul_lt_mul_of_pos_left hψt₁_gt (by linarith)
    linarith
  have ht₂pos : 0 < t₂ := lt_trans ht₁pos ht₁₂
  exact (div_lt_div_iff₀ ht₂pos ht₁pos).mpr (by linarith)

lemma P3bF_fp_scale (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∃ θ₀ c C : ℝ, 0 < θ₀ ∧ 0 < c ∧ 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      ∃ u : ℝ, (0 < u ∧ u < 1 ∧ u = deriv (phi S) ((tau S + θ) * u)) ∧
        (∀ u' : ℝ, 0 < u' → u' < 1 → u' = deriv (phi S) ((tau S + θ) * u') → u' = u) ∧
        c * θ ^ (1 / (2 * (p : ℝ) - 2)) ≤ u ∧ u ≤ C * θ ^ (1 / (2 * (p : ℝ) - 2)) ∧
        c * θ ^ ((p : ℝ) / ((p : ℝ) - 1)) ≤ θ * u ^ 2 ∧
        θ * u ^ 2 ≤ C * θ ^ ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hp2 : 2 ≤ p := hp.1
  have hpmin : ∀ j : ℕ, 2 ≤ j → j < p → iteratedDeriv (2 * j) (phi S) 0 = 0 := hp.2.1
  have hpneg : iteratedDeriv (2 * p) (phi S) 0 < 0 := hp.2.2
  let v : ℝ := variance S
  let τ : ℝ := tau S
  have hvpos : 0 < v := P3bF_variance_pos S
  have hτpos : 0 < τ := P3bF_tau_pos S
  have hτv : τ * v = 1 := P3bF_tau_mul_variance S
  let ψ : ℝ → ℝ := deriv (phi S)
  have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    have h1 : ψ = iteratedDeriv 1 (phi S) := iteratedDeriv_one.symm
    rw [h1]
    exact P3bF_contDiff_iteratedDeriv 1 (P3bF_phi_contDiff S)
  obtain ⟨C₁, hC₁0, hTψ⟩ := P3bF_taylor_bound_Icc ψ hψ_cd (2 * p - 1)
  let b : ℝ := -iteratedDeriv (2 * p) (phi S) 0 / ((2 * p - 1)! : ℝ)
  have hbpos : 0 < b := by
    have hneg_pos : 0 < -iteratedDeriv (2 * p) (phi S) 0 := by linarith
    positivity
  have hψPoly : ∀ t : ℝ,
      (∑ k ∈ Finset.range (2 * p - 1 + 1), (iteratedDeriv k ψ 0 / (k ! : ℝ)) * t ^ k) =
        v * t - b * t ^ (2 * p - 1) := by
    intro t
    have hrange : 2 * p - 1 + 1 = 2 * p := by omega
    rw [hrange]
    have hmem1 : 1 ∈ Finset.range (2 * p) := by rw [Finset.mem_range]; omega
    have hmem2 : 2 * p - 1 ∈ (Finset.range (2 * p)).erase 1 := by
      rw [Finset.mem_erase, Finset.mem_range]; omega
    rw [← Finset.add_sum_erase _ _ hmem1, ← Finset.add_sum_erase _ _ hmem2]
    have hrest : (∑ k ∈ ((Finset.range (2 * p)).erase 1).erase (2 * p - 1),
        (iteratedDeriv k ψ 0 / (k ! : ℝ)) * t ^ k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_range] at hk
      have hk0 : iteratedDeriv k ψ 0 = 0 := by
        dsimp [ψ]
        rw [← iteratedDeriv_succ']
        rcases Nat.even_or_odd (k + 1) with ⟨j, hj⟩ | ⟨j, hj⟩
        · have hj0 : j ≠ 0 := by omega
          have hj1 : j ≠ 1 := by omega
          have hj2 : 2 ≤ j := by omega
          have hjp : j < p := by omega
          rw [show k + 1 = 2 * j by omega]
          exact hpmin j hj2 hjp
        · rw [hj]
          exact P3bF_iteratedDeriv_odd_zero S j
      rw [hk0]; ring
    have hterm1 : (iteratedDeriv 1 ψ 0 / (1 ! : ℝ)) * t ^ 1 = v * t := by
      dsimp [ψ, v]
      rw [← iteratedDeriv_succ', P3bF_iteratedDeriv_two_zero]
      norm_num
    have hterm2 : (iteratedDeriv (2 * p - 1) ψ 0 / ((2 * p - 1)! : ℝ)) * t ^ (2 * p - 1) =
        -b * t ^ (2 * p - 1) := by
      dsimp [ψ, b]
      rw [← iteratedDeriv_succ', show (2 * p - 1) + 1 = 2 * p by omega]
      ring
    rw [hterm1, hterm2, hrest, add_zero]
    ring
  have hψ_bound : ∀ t : ℝ, |t| ≤ 1 → |ψ t - (v * t - b * t ^ (2 * p - 1))| ≤ C₁ * |t| ^ (2 * p) := by
    intro t ht
    have h := hTψ t ht
    rw [hψPoly t, show (2 * p - 1 + 1) = 2 * p by omega] at h
    exact h
  let tStar : ℝ := min 1 (b / (2 * (C₁ + 1)))
  have htStar_pos : 0 < tStar := lt_min (by norm_num) (div_pos hbpos (by linarith))
  have htStar_le1 : tStar ≤ 1 := min_le_left _ _
  have htStar_le_b : tStar ≤ b / (2 * (C₁ + 1)) := min_le_right _ _
  have hψ_sandwich : ∀ t : ℝ, 0 ≤ t → t ≤ tStar →
      v * t - (3 * b / 2) * t ^ (2 * p - 1) ≤ ψ t ∧
        ψ t ≤ v * t - (b / 2) * t ^ (2 * p - 1) := by
    intro t ht0 htle
    have htabs : |t| ≤ 1 := abs_le.mpr ⟨by linarith, htle.trans htStar_le1⟩
    have hbnd := hψ_bound t htabs
    rw [abs_of_nonneg ht0] at hbnd
    have hC1t : C₁ * t ≤ b / 2 := by
      calc
        C₁ * t ≤ (C₁ + 1) * t := mul_le_mul_of_nonneg_right (by linarith) ht0
        _ ≤ (C₁ + 1) * (b / (2 * (C₁ + 1))) := mul_le_mul_of_nonneg_left (htle.trans htStar_le_b) (by linarith)
        _ = b / 2 := by field_simp [show C₁ + 1 ≠ 0 by linarith]
    have hpow : t ^ (2 * p) = t ^ (2 * p - 1) * t := by
      rw [← pow_succ, show (2 * p - 1) + 1 = 2 * p by omega]
    have herr : C₁ * t ^ (2 * p) ≤ (b / 2) * t ^ (2 * p - 1) := by
      calc
        C₁ * t ^ (2 * p) = (C₁ * t) * t ^ (2 * p - 1) := by rw [hpow]; ring
        _ ≤ (b / 2) * t ^ (2 * p - 1) := mul_le_mul_of_nonneg_right hC1t (pow_nonneg ht0 _)
    have habs := abs_le.mp (hbnd.trans herr)
    constructor <;> linarith
  let q : ℝ := 2 * (p : ℝ) - 2
  have hq_eq : q = ((2 * p - 2 : ℕ) : ℝ) := by push_cast [show 2 ≤ 2 * p by omega]; ring
  have hq_pos : 0 < q := by
    dsimp [q]
    have h2p : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  let c₁ : ℝ := (v / (2 * b * (2 * τ) ^ (2 * p - 1))) ^ (1 / q)
  let C₁' : ℝ := (4 * v / (b * τ ^ (2 * p - 1))) ^ (1 / q)
  have hc₁_pos : 0 < c₁ := by dsimp [c₁]; positivity
  have hC₁'_pos : 0 < C₁' := by dsimp [C₁']; positivity
  have hc₁_lt_C₁' : c₁ < C₁' := by
    apply Real.rpow_lt_rpow (by positivity) _ (div_pos one_pos hq_pos)
    have hpow_le : τ ^ (2 * p - 1) ≤ (2 * τ) ^ (2 * p - 1) :=
      pow_le_pow_left₀ hτpos.le (by linarith) _
    have hnum_lt : v / (2 * b * (2 * τ) ^ (2 * p - 1)) ≤ v / (2 * b * τ ^ (2 * p - 1)) :=
      div_le_div_of_nonneg_left hvpos.le (by positivity) (mul_le_mul_of_nonneg_left hpow_le (by positivity))
    have hhalf_lt : v / (2 * b * τ ^ (2 * p - 1)) < 4 * v / (b * τ ^ (2 * p - 1)) := by
      have hpos : 0 < v / (b * τ ^ (2 * p - 1)) := by positivity
      calc
        v / (2 * b * τ ^ (2 * p - 1)) = (1 / 2) * (v / (b * τ ^ (2 * p - 1))) := by ring
        _ < 4 * (v / (b * τ ^ (2 * p - 1))) := by linarith
        _ = 4 * v / (b * τ ^ (2 * p - 1)) := by ring
    exact lt_of_le_of_lt hnum_lt hhalf_lt
  let θ₀ : ℝ := min (min τ 1) (min ((tStar / (2 * τ * C₁')) ^ (2 * p - 2)) ((1 / (2 * C₁')) ^ (2 * p - 2)))
  have hθ₀_pos : 0 < θ₀ := by
    refine lt_min (lt_min hτpos (by norm_num)) (lt_min ?_ ?_)
    · exact pow_pos (div_pos htStar_pos (by positivity)) _
    · exact pow_pos (div_pos one_pos (by positivity)) _
  let c : ℝ := min c₁ (c₁ ^ 2)
  let C : ℝ := max C₁' (C₁' ^ 2)
  have hc_pos : 0 < c := lt_min hc₁_pos (sq_pos_of_pos hc₁_pos)
  have hC_pos : 0 < C := lt_of_lt_of_le hC₁'_pos (le_max_left _ _)
  refine ⟨θ₀, c, C, hθ₀_pos, hc_pos, hC_pos, fun θ hθpos hθle => ?_⟩
  have hθτ : θ ≤ τ := hθle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hθt : θ ≤ (tStar / (2 * τ * C₁')) ^ (2 * p - 2) :=
    hθle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθone : θ ≤ (1 / (2 * C₁')) ^ (2 * p - 2) :=
    hθle.trans ((min_le_right _ _).trans (min_le_right _ _))
  let θq : ℝ := θ ^ (1 / q)
  have hθq_pos : 0 < θq := Real.rpow_pos_of_pos hθpos _
  have hθq_t : θq ≤ tStar / (2 * τ * C₁') := by
    have hr := Real.rpow_le_rpow hθpos.le hθt (div_pos one_pos hq_pos).le
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← hq_eq,
      mul_one_div_cancel (ne_of_gt hq_pos), Real.rpow_one] at hr
    exact hr
  have hθq_one : θq ≤ 1 / (2 * C₁') := by
    have hr := Real.rpow_le_rpow hθpos.le hθone (div_pos one_pos hq_pos).le
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← hq_eq,
      mul_one_div_cancel (ne_of_gt hq_pos), Real.rpow_one] at hr
    exact hr
  let uMinus : ℝ := c₁ * θq
  let uPlus : ℝ := C₁' * θq
  have huM_pos : 0 < uMinus := mul_pos hc₁_pos hθq_pos
  have huM_lt_uP : uMinus < uPlus := mul_lt_mul_of_pos_right hc₁_lt_C₁' hθq_pos
  have huP_lt1 : uPlus < 1 := by
    have hle : uPlus ≤ 1 / 2 := by
      dsimp [uPlus]
      calc
        C₁' * θq ≤ C₁' * (1 / (2 * C₁')) := mul_le_mul_of_nonneg_left hθq_one hC₁'_pos.le
        _ = 1 / 2 := by field_simp [ne_of_gt hC₁'_pos]
    linarith
  let β : ℝ := τ + θ
  have hβpos : 0 < β := by linarith
  have hβgt : τ < β := by linarith
  have hβle : β ≤ 2 * τ := by linarith
  have hβuP_le : β * uPlus ≤ tStar := by
    calc
      β * uPlus ≤ (2 * τ) * uPlus := mul_le_mul_of_nonneg_right hβle (by positivity)
      _ = (2 * τ * C₁') * θq := by dsimp [uPlus]; ring
      _ ≤ (2 * τ * C₁') * (tStar / (2 * τ * C₁')) :=
          mul_le_mul_of_nonneg_left hθq_t (by positivity)
      _ = tStar := by field_simp [ne_of_gt hτpos, ne_of_gt hC₁'_pos]
  have hβuM_le : β * uMinus ≤ tStar :=
    le_trans (mul_le_mul_of_nonneg_left huM_lt_uP.le hβpos.le) hβuP_le
  have hpow_uM : uMinus ^ (2 * p - 2) = (v / (2 * b * (2 * τ) ^ (2 * p - 1))) * θ := by
    dsimp [uMinus, θq]
    rw [mul_pow, ← Real.rpow_natCast c₁, ← Real.rpow_natCast (θ ^ (1 / q)),
      ← hq_eq, ← Real.rpow_mul (by positivity), ← Real.rpow_mul hθpos.le,
      one_div_mul_cancel (ne_of_gt hq_pos), Real.rpow_one, Real.rpow_one]
  have hpow_uP : uPlus ^ (2 * p - 2) = (4 * v / (b * τ ^ (2 * p - 1))) * θ := by
    dsimp [uPlus, θq]
    rw [mul_pow, ← Real.rpow_natCast C₁', ← Real.rpow_natCast (θ ^ (1 / q)),
      ← hq_eq, ← Real.rpow_mul (by positivity), ← Real.rpow_mul hθpos.le,
      one_div_mul_cancel (ne_of_gt hq_pos), Real.rpow_one, Real.rpow_one]
  have hgt_M : uMinus < ψ (β * uMinus) := by
    have hs := hψ_sandwich (β * uMinus) (by positivity) hβuM_le
    have hs1 := hs.1
    have hpow_split : (β * uMinus) ^ (2 * p - 1) = β ^ (2 * p - 1) * uMinus ^ (2 * p - 2) * uMinus := by
      rw [mul_pow]
      have hsp : uMinus ^ (2 * p - 1) = uMinus ^ (2 * p - 2) * uMinus := by
        rw [← pow_succ, show (2 * p - 2) + 1 = 2 * p - 1 by omega]
      rw [hsp]; ring
    have hβ_pow : β ^ (2 * p - 1) ≤ (2 * τ) ^ (2 * p - 1) :=
      pow_le_pow_left₀ hβpos.le hβle _
    have hterm_le : (3 * b / 2) * (β * uMinus) ^ (2 * p - 1) ≤ (3 / 4) * v * θ * uMinus := by
      rw [hpow_split, hpow_uM]
      calc
        (3 * b / 2) * (β ^ (2 * p - 1) * ((v / (2 * b * (2 * τ) ^ (2 * p - 1))) * θ) * uMinus)
            ≤ (3 * b / 2) * ((2 * τ) ^ (2 * p - 1) * ((v / (2 * b * (2 * τ) ^ (2 * p - 1))) * θ) * uMinus) := by
              gcongr
        _ = (3 / 4) * v * θ * uMinus := by
              field_simp [ne_of_gt hbpos, ne_of_gt hτpos]
              ring
    have hlin : v * (β * uMinus) = uMinus + v * θ * uMinus := by
      dsimp [β]
      calc
        v * ((τ + θ) * uMinus) = (τ * v) * uMinus + v * θ * uMinus := by ring
        _ = uMinus + v * θ * uMinus := by rw [hτv, one_mul]
    have hpos_vθu : 0 < v * θ * uMinus := by positivity
    linarith
  have hlt_P : ψ (β * uPlus) < uPlus := by
    have hs := (hψ_sandwich (β * uPlus) (by positivity) hβuP_le).2
    have hpow_split : (β * uPlus) ^ (2 * p - 1) = β ^ (2 * p - 1) * uPlus ^ (2 * p - 2) * uPlus := by
      rw [mul_pow]
      have hsp : uPlus ^ (2 * p - 1) = uPlus ^ (2 * p - 2) * uPlus := by
        rw [← pow_succ, show (2 * p - 2) + 1 = 2 * p - 1 by omega]
      rw [hsp]; ring
    have hβ_pow : τ ^ (2 * p - 1) ≤ β ^ (2 * p - 1) :=
      pow_le_pow_left₀ hτpos.le hβgt.le _
    have hterm_ge : 2 * v * θ * uPlus ≤ (b / 2) * (β * uPlus) ^ (2 * p - 1) := by
      rw [hpow_split, hpow_uP]
      calc
        2 * v * θ * uPlus
            = (b / 2) * (τ ^ (2 * p - 1) * ((4 * v / (b * τ ^ (2 * p - 1))) * θ) * uPlus) := by
              field_simp [ne_of_gt hbpos, ne_of_gt hτpos]
              ring
        _ ≤ (b / 2) * (β ^ (2 * p - 1) * ((4 * v / (b * τ ^ (2 * p - 1))) * θ) * uPlus) := by
              gcongr
    have hlin : v * (β * uPlus) = uPlus + v * θ * uPlus := by
      dsimp [β]
      calc
        v * ((τ + θ) * uPlus) = (τ * v) * uPlus + v * θ * uPlus := by ring
        _ = uPlus + v * θ * uPlus := by rw [hτv, one_mul]
    have hpos_vθu : 0 < v * θ * uPlus := by positivity
    linarith
  let g : ℝ → ℝ := fun u => ψ (β * u) - u
  have hg_cont : ContinuousOn g (Set.Icc uMinus uPlus) := by
    have hψ_cont : Continuous ψ := hψ_cd.continuous
    exact ((hψ_cont.comp (continuous_const.mul continuous_id)).sub continuous_id).continuousOn
  have h0_mem : (0 : ℝ) ∈ Set.Icc (g uPlus) (g uMinus) := by
    refine ⟨?_, ?_⟩ <;> dsimp [g] <;> linarith
  obtain ⟨u, huIcc, hgu⟩ := intermediate_value_Icc' huM_lt_uP.le hg_cont h0_mem
  have hu_pos : 0 < u := lt_of_lt_of_le huM_pos huIcc.1
  have hu_lt1 : u < 1 := lt_of_le_of_lt huIcc.2 huP_lt1
  have hu_eq : u = ψ (β * u) := by dsimp [g] at hgu; linarith
  have huniq : ∀ u' : ℝ, 0 < u' → u' < 1 → u' = ψ (β * u') → u' = u := by
    intro u' hu'pos _ hu'eq
    rcases lt_trichotomy u' u with hlt | rfl | hgt
    · have hanti := P3bF_deriv_phi_div_strictAnti S hS p hp (β * u') (β * u)
        (mul_pos hβpos hu'pos) (mul_lt_mul_of_pos_left hlt hβpos)
      have hlhs : ψ (β * u) / (β * u) = 1 / β := by
        rw [← hu_eq]; field_simp [ne_of_gt hβpos, ne_of_gt hu_pos]
      have hrhs : ψ (β * u') / (β * u') = 1 / β := by
        rw [← hu'eq]; field_simp [ne_of_gt hβpos, ne_of_gt hu'pos]
      change ψ (β * u) / (β * u) < ψ (β * u') / (β * u') at hanti
      linarith
    · rfl
    · have hanti := P3bF_deriv_phi_div_strictAnti S hS p hp (β * u) (β * u')
        (mul_pos hβpos hu_pos) (mul_lt_mul_of_pos_left hgt hβpos)
      have hlhs : ψ (β * u) / (β * u) = 1 / β := by
        rw [← hu_eq]; field_simp [ne_of_gt hβpos, ne_of_gt hu_pos]
      have hrhs : ψ (β * u') / (β * u') = 1 / β := by
        rw [← hu'eq]; field_simp [ne_of_gt hβpos, ne_of_gt hu'pos]
      change ψ (β * u') / (β * u') < ψ (β * u) / (β * u) at hanti
      linarith
  have hθ_pow_id : θ * θq ^ 2 = θ ^ ((p : ℝ) / ((p : ℝ) - 1)) := by
    dsimp [θq, q]
    have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have hp1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
    have hrpow : (θ ^ (1 / (2 * (p : ℝ) - 2))) ^ (2 : ℕ) =
        θ ^ (1 / (2 * (p : ℝ) - 2) * (2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hθpos.le]
      push_cast
      rfl
    rw [hrpow]
    nth_rw 1 [← Real.rpow_one θ]
    rw [← Real.rpow_add hθpos]
    congr 1
    field_simp [hp1_ne]
    ring
  refine ⟨u, ⟨hu_pos, hu_lt1, hu_eq⟩, huniq, ?_, ?_, ?_, ?_⟩
  · calc
      c * θ ^ (1 / (2 * (p : ℝ) - 2)) ≤ c₁ * θq :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hθq_pos.le
      _ ≤ u := huIcc.1
  · calc
      u ≤ C₁' * θq := huIcc.2
      _ ≤ C * θ ^ (1 / (2 * (p : ℝ) - 2)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hθq_pos.le
  · calc
      c * θ ^ ((p : ℝ) / ((p : ℝ) - 1)) ≤ c₁ ^ 2 * (θ * θq ^ 2) := by
        rw [hθ_pow_id]
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = θ * uMinus ^ 2 := by dsimp [uMinus]; ring
      _ ≤ θ * u ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hθpos.le
        exact sq_le_sq' (by linarith) huIcc.1
  · calc
      θ * u ^ 2 ≤ θ * uPlus ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hθpos.le
        exact sq_le_sq' (by linarith) huIcc.2
      _ = C₁' ^ 2 * (θ * θq ^ 2) := by dsimp [uPlus]; ring
      _ ≤ C * θ ^ ((p : ℝ) / ((p : ℝ) - 1)) := by
        rw [hθ_pow_id]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end CritWinSpin

open CritWinSpin

theorem solution (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∃ θ₀ c C : ℝ, 0 < θ₀ ∧ 0 < c ∧ 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      ∃ u : ℝ, (0 < u ∧ u < 1 ∧ u = deriv (phi S) ((tau S + θ) * u)) ∧
        (∀ u' : ℝ, 0 < u' → u' < 1 → u' = deriv (phi S) ((tau S + θ) * u') → u' = u) ∧
        c * θ ^ (1 / (2 * (p : ℝ) - 2)) ≤ u ∧ u ≤ C * θ ^ (1 / (2 * (p : ℝ) - 2)) ∧
        c * θ ^ ((p : ℝ) / ((p : ℝ) - 1)) ≤ θ * u ^ 2 ∧
        θ * u ^ 2 ≤ C * θ ^ ((p : ℝ) / ((p : ℝ) - 1)) :=
  P3bF_fp_scale S p hS hp
