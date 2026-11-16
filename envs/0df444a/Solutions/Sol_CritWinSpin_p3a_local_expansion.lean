-- Prove2me | solution 1 for CritWinSpin.p3a_local_expansion
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-15T22:18:27.947806+00:00
-- url     : https://prove2.me/submissions/0050bafa-c4ce-4e0f-bd29-086f4f1f82ad

import Mathlib
import Definitions.Def_CritWinSpin_SpinLaw
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
open scoped BigOperators Nat

namespace CritWinSpin

noncomputable def P3aL_Z (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))

noncomputable def P3aL_Z1 (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))

noncomputable def P3aL_Z2 (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))

lemma P3aL_Z_pos (S : SpinLaw) (t : ℝ) : 0 < P3aL_Z S t := by
  unfold P3aL_Z
  apply Finset.sum_pos'
  · intro x hx
    exact mul_nonneg (by exact_mod_cast (le_of_lt (S.pos x hx))) (Real.exp_pos _).le
  · refine ⟨1, S.one_mem, ?_⟩
    exact mul_pos (by exact_mod_cast S.pos 1 S.one_mem) (Real.exp_pos _)

lemma P3aL_Z_zero (S : SpinLaw) : P3aL_Z S 0 = 1 := by
  unfold P3aL_Z
  simp only [zero_mul, Real.exp_zero, mul_one]
  exact_mod_cast S.sum_one

lemma P3aL_variance_pos (S : SpinLaw) : 0 < variance S := by
  have hvQ : 0 < varQ S := by
    have h1 : 0 < (1 : ℚ) ^ 2 * S.ρ 1 := by simpa using S.pos 1 S.one_mem
    have hnonneg : ∀ x ∈ S.A, 0 ≤ x ^ 2 * S.ρ x := fun x hx =>
      mul_nonneg (sq_nonneg x) (S.pos x hx).le
    have hle : (1 : ℚ) ^ 2 * S.ρ 1 ≤ varQ S := by
      rw [varQ]
      exact Finset.single_le_sum hnonneg S.one_mem
    exact lt_of_lt_of_le h1 hle
  exact Rat.cast_pos.mpr hvQ

lemma P3aL_tau_mul_variance (S : SpinLaw) : tau S * variance S = 1 := by
  have hvpos : 0 < variance S := P3aL_variance_pos S
  have hvne : variance S ≠ 0 := ne_of_gt hvpos
  have htau : tau S = 1 / variance S := by
    unfold tau tauQ variance
    push_cast
    rfl
  rw [htau]
  field_simp [hvne]

lemma P3aL_tau_pos (S : SpinLaw) : 0 < tau S := by
  have h1 := P3aL_tau_mul_variance S
  have hv := P3aL_variance_pos S
  nlinarith

lemma P3aL_Z1_zero (S : SpinLaw) : P3aL_Z1 S 0 = 0 := by
  unfold P3aL_Z1
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

lemma P3aL_Z2_zero (S : SpinLaw) : P3aL_Z2 S 0 = variance S := by
  unfold P3aL_Z2 variance varQ
  simp only [zero_mul, Real.exp_zero, mul_one]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma P3aL_hasDerivAt_Z (S : SpinLaw) (t : ℝ) : HasDerivAt (P3aL_Z S) (P3aL_Z1 S t) t := by
  unfold P3aL_Z P3aL_Z1
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

lemma P3aL_hasDerivAt_Z1 (S : SpinLaw) (t : ℝ) : HasDerivAt (P3aL_Z1 S) (P3aL_Z2 S t) t := by
  unfold P3aL_Z1 P3aL_Z2
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

lemma P3aL_hasDerivAt_phi (S : SpinLaw) (t : ℝ) :
    HasDerivAt (phi S) (P3aL_Z1 S t / P3aL_Z S t) t := by
  change HasDerivAt (fun s => Real.log (P3aL_Z S s)) (P3aL_Z1 S t / P3aL_Z S t) t
  exact (P3aL_hasDerivAt_Z S t).log (ne_of_gt (P3aL_Z_pos S t))

lemma P3aL_deriv_phi (S : SpinLaw) : deriv (phi S) = fun t => P3aL_Z1 S t / P3aL_Z S t := by
  funext t
  exact (P3aL_hasDerivAt_phi S t).deriv

lemma P3aL_hasDerivAt_deriv_phi (S : SpinLaw) (t : ℝ) :
    HasDerivAt (deriv (phi S))
      ((P3aL_Z2 S t * P3aL_Z S t - P3aL_Z1 S t * P3aL_Z1 S t) / P3aL_Z S t ^ 2) t := by
  rw [P3aL_deriv_phi]
  exact (P3aL_hasDerivAt_Z1 S t).div (P3aL_hasDerivAt_Z S t) (ne_of_gt (P3aL_Z_pos S t))

lemma P3aL_Z2Z_sub_Z1sq_pos (S : SpinLaw) (t : ℝ) :
    0 < P3aL_Z2 S t * P3aL_Z S t - P3aL_Z1 S t * P3aL_Z1 S t := by
  let w : ℚ → ℝ := fun x => (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))
  have hw_pos : ∀ x ∈ S.A, 0 < w x := fun x hx =>
    mul_pos (by exact_mod_cast S.pos x hx) (Real.exp_pos _)
  have hid : 2 * (P3aL_Z2 S t * P3aL_Z S t - P3aL_Z1 S t * P3aL_Z1 S t) =
      ∑ x ∈ S.A, ∑ y ∈ S.A, w x * w y * ((x : ℝ) - (y : ℝ)) ^ 2 := by
    have hA : (∑ x ∈ S.A, ∑ y ∈ S.A, w x * w y * ((x : ℝ) - (y : ℝ)) ^ 2) =
        (∑ x ∈ S.A, ∑ y ∈ S.A, (w x * (x : ℝ) ^ 2) * w y) +
        (∑ x ∈ S.A, ∑ y ∈ S.A, w x * (w y * (y : ℝ) ^ 2)) -
        2 * (∑ x ∈ S.A, ∑ y ∈ S.A, (w x * (x : ℝ)) * (w y * (y : ℝ))) := by
      have h1 : ∀ x y : ℚ, w x * w y * ((x : ℝ) - (y : ℝ)) ^ 2 =
          (w x * (x : ℝ) ^ 2) * w y + w x * (w y * (y : ℝ) ^ 2) -
            2 * ((w x * (x : ℝ)) * (w y * (y : ℝ))) := fun x y => by ring
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hZ : P3aL_Z S t = ∑ x ∈ S.A, w x := rfl
    have hZ1 : P3aL_Z1 S t = ∑ x ∈ S.A, w x * (x : ℝ) := by
      unfold P3aL_Z1
      apply Finset.sum_congr rfl
      intro x _
      dsimp [w]
      ring
    have hZ2 : P3aL_Z2 S t = ∑ x ∈ S.A, w x * (x : ℝ) ^ 2 := by
      unfold P3aL_Z2
      apply Finset.sum_congr rfl
      intro x _
      dsimp [w]
      ring
    rw [hA]
    have p1 : (∑ x ∈ S.A, ∑ y ∈ S.A, (w x * (x : ℝ) ^ 2) * w y) = P3aL_Z2 S t * P3aL_Z S t := by
      rw [hZ2, hZ, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.mul_sum]
    have p2 : (∑ x ∈ S.A, ∑ y ∈ S.A, w x * (w y * (y : ℝ) ^ 2)) = P3aL_Z S t * P3aL_Z2 S t := by
      rw [hZ, hZ2, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.mul_sum]
    have p3 : (∑ x ∈ S.A, ∑ y ∈ S.A, (w x * (x : ℝ)) * (w y * (y : ℝ))) =
        P3aL_Z1 S t * P3aL_Z1 S t := by
      rw [hZ1, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.mul_sum]
    rw [p1, p2, p3]
    ring
  have hpos2 : 0 < ∑ x ∈ S.A, ∑ y ∈ S.A, w x * w y * ((x : ℝ) - (y : ℝ)) ^ 2 := by
    apply Finset.sum_pos'
    · intro x hx
      apply Finset.sum_nonneg
      intro y hy
      exact mul_nonneg (mul_nonneg (hw_pos x hx).le (hw_pos y hy).le) (sq_nonneg _)
    · refine ⟨1, S.one_mem, ?_⟩
      apply Finset.sum_pos'
      · intro y hy
        exact mul_nonneg (mul_nonneg (hw_pos 1 S.one_mem).le (hw_pos y hy).le) (sq_nonneg _)
      · refine ⟨-1, S.neg_one_mem, ?_⟩
        have h1pos := hw_pos 1 S.one_mem
        have hm1pos := hw_pos (-1) S.neg_one_mem
        norm_num
        positivity
  linarith

lemma P3aL_deriv_phi_strictMono (S : SpinLaw) : StrictMono (deriv (phi S)) := by
  apply strictMono_of_hasDerivAt_pos (P3aL_hasDerivAt_deriv_phi S)
  intro t
  exact div_pos (P3aL_Z2Z_sub_Z1sq_pos S t) (sq_pos_of_pos (P3aL_Z_pos S t))

lemma P3aL_rateI_at_deriv (S : SpinLaw) (t₀ : ℝ) :
    rateI S (deriv (phi S) t₀) = t₀ * deriv (phi S) t₀ - phi S t₀ := by
  let m := deriv (phi S) t₀
  let h : ℝ → ℝ := fun t => t * m - phi S t
  have hdiff : ∀ t : ℝ, HasDerivAt h (m - deriv (phi S) t) t := by
    intro t
    have hd1 : HasDerivAt (fun s => s * m) m t := by simpa using (hasDerivAt_id t).mul_const m
    have hd2 : HasDerivAt (phi S) (deriv (phi S) t) t := by
      rw [P3aL_deriv_phi]
      exact P3aL_hasDerivAt_phi S t
    exact hd1.sub hd2
  have hmono : MonotoneOn h (Set.Iic t₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic t₀)
    · exact fun t _ => (hdiff t).continuousAt.continuousWithinAt
    · exact fun t _ => (hdiff t).differentiableAt.differentiableWithinAt
    · intro t ht
      have htle : t ≤ t₀ := (interior_Iic.subset ht).le
      rw [(hdiff t).deriv]
      have hle : deriv (phi S) t ≤ m := (P3aL_deriv_phi_strictMono S).monotone htle
      linarith
  have hanti : AntitoneOn h (Set.Ici t₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀)
    · exact fun t _ => (hdiff t).continuousAt.continuousWithinAt
    · exact fun t _ => (hdiff t).differentiableAt.differentiableWithinAt
    · intro t ht
      have htge : t₀ ≤ t := (interior_Ici.subset ht).le
      rw [(hdiff t).deriv]
      have hge : m ≤ deriv (phi S) t := (P3aL_deriv_phi_strictMono S).monotone htge
      linarith
  have hmax : ∀ t : ℝ, h t ≤ h t₀ := by
    intro t
    rcases le_total t t₀ with hle | hge
    · exact hmono hle (Set.mem_Iic.mpr le_rfl) hle
    · exact hanti (Set.mem_Ici.mpr le_rfl) hge hge
  have hbdd : BddAbove (Set.range h) := ⟨h t₀, by rintro _ ⟨t, rfl⟩; exact hmax t⟩
  unfold rateI
  exact le_antisymm (ciSup_le hmax) (le_ciSup hbdd t₀)

lemma P3aL_phi_analyticOnNhd (S : SpinLaw) : AnalyticOnNhd ℝ (phi S) Set.univ := by
  intro t _
  change AnalyticAt ℝ (fun s => Real.log (P3aL_Z S s)) t
  have hZ : AnalyticAt ℝ (P3aL_Z S) t := by
    unfold P3aL_Z
    refine Finset.analyticAt_fun_sum S.A fun x _ => ?_
    exact analyticAt_const.mul (analyticAt_rexp.comp ((analyticAt_id : AnalyticAt ℝ id t).mul analyticAt_const))
  exact (analyticAt_log (P3aL_Z_pos S t)).comp hZ

lemma P3aL_phi_contDiff (S : SpinLaw) : ContDiff ℝ ⊤ (phi S) :=
  (P3aL_phi_analyticOnNhd S).contDiff

lemma P3aL_phi_zero (S : SpinLaw) : phi S 0 = 0 := by
  change Real.log (P3aL_Z S 0) = 0
  rw [P3aL_Z_zero, Real.log_one]

lemma P3aL_iteratedDeriv_one_zero (S : SpinLaw) : iteratedDeriv 1 (phi S) 0 = 0 := by
  rw [iteratedDeriv_one, P3aL_deriv_phi]
  dsimp only
  rw [P3aL_Z1_zero, P3aL_Z_zero]
  norm_num

lemma P3aL_iteratedDeriv_two_zero (S : SpinLaw) : iteratedDeriv 2 (phi S) 0 = variance S := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hd := P3aL_hasDerivAt_deriv_phi S 0
  rw [hd.deriv, P3aL_Z2_zero, P3aL_Z_zero, P3aL_Z1_zero]
  norm_num

lemma P3aL_phi_even (S : SpinLaw) (t : ℝ) : phi S (-t) = phi S t := by
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

lemma P3aL_iteratedDeriv_even_symm (S : SpinLaw) (n : ℕ) :
    ∀ t : ℝ, iteratedDeriv n (phi S) (-t) = (-1 : ℝ) ^ n * iteratedDeriv n (phi S) t := by
  induction n with
  | zero => intro t; simp [P3aL_phi_even S t]
  | succ n ih =>
    intro t
    have hdiff : Differentiable ℝ (iteratedDeriv n (phi S)) :=
      (P3aL_phi_contDiff S).differentiable_iteratedDeriv n
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

lemma P3aL_iteratedDeriv_odd_zero (S : SpinLaw) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (phi S) 0 = 0 := by
  have h := P3aL_iteratedDeriv_even_symm S (2 * k + 1) 0
  simp only [neg_zero] at h
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
  rw [hpow] at h
  linarith

lemma P3aL_iteratedDeriv_add (m k : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv m (iteratedDeriv k f) = iteratedDeriv (m + k) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add_apply]

lemma P3aL_contDiff_iteratedDeriv (k : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv k f) := by
  apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
  intro m _
  rw [P3aL_iteratedDeriv_add]
  exact hf.differentiable_iteratedDeriv (m + k)
    (by exact_mod_cast (WithTop.coe_lt_top ((m + k : ℕ) : ℕ∞) : (((m + k : ℕ) : ℕ∞) : WithTop ℕ∞) < ⊤))

lemma P3aL_taylor_bound_Icc (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
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
      (hf.of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffOn
    obtain ⟨x', hx'mem, hx'eq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv htne hfC
    have hu : UniqueDiffOn ℝ (Set.uIcc 0 t) := uniqueDiffOn_uIcc htne
    have htay : taylorWithinEval f n (Set.uIcc 0 t) 0 t =
        ∑ k ∈ Finset.range (n + 1), (iteratedDeriv k f 0 / (k ! : ℝ)) * t ^ k := by
      rw [taylor_within_apply]
      apply Finset.sum_congr rfl
      intro k _
      have hwithin : iteratedDerivWithin k f (Set.uIcc 0 t) 0 = iteratedDeriv k f 0 :=
        iteratedDerivWithin_eq_iteratedDeriv hu
          (hf.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt Set.left_mem_uIcc
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
          ≤ max 0 B * |t| ^ (n + 1) / ((n + 1)! : ℝ) := by
            gcongr
      _ = M * |t| ^ (n + 1) := by dsimp [M]; ring

lemma P3aL_abs_pow_sub_le (m : ℕ) (a b R : ℝ) (ha : |a| ≤ R) (hb : |b| ≤ R) :
    |a ^ m - b ^ m| ≤ (m : ℝ) * R ^ (m - 1) * |a - b| := by
  have hR : 0 ≤ R := le_trans (abs_nonneg a) ha
  induction m with
  | zero => simp
  | succ k ih =>
    have hid : a ^ (k + 1) - b ^ (k + 1) = (a - b) * a ^ k + b * (a ^ k - b ^ k) := by ring
    rw [hid]
    have hak : |a ^ k| ≤ R ^ k := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg a) ha k
    have h1 : |(a - b) * a ^ k| ≤ |a - b| * R ^ k := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hak (abs_nonneg _)
    have h2 : |b * (a ^ k - b ^ k)| ≤ R * ((k : ℝ) * R ^ (k - 1) * |a - b|) := by
      rw [abs_mul]
      exact mul_le_mul hb ih (abs_nonneg _) hR
    have hpow : R * ((k : ℝ) * R ^ (k - 1) * |a - b|) ≤ (k : ℝ) * R ^ k * |a - b| := by
      cases k with
      | zero => simp
      | succ k' =>
        have this : R * R ^ k' = R ^ (k' + 1) := by rw [pow_succ']
        have heq : R * (((k' + 1 : ℕ) : ℝ) * R ^ k' * |a - b|) =
            ((k' + 1 : ℕ) : ℝ) * R ^ (k' + 1) * |a - b| := by
          calc
            R * (((k' + 1 : ℕ) : ℝ) * R ^ k' * |a - b|)
                = ((k' + 1 : ℕ) : ℝ) * (R * R ^ k') * |a - b| := by ring
            _ = ((k' + 1 : ℕ) : ℝ) * R ^ (k' + 1) * |a - b| := by rw [this]
        exact heq.le
    have hsum : |(a - b) * a ^ k + b * (a ^ k - b ^ k)| ≤
        |a - b| * R ^ k + (k : ℝ) * R ^ k * |a - b| :=
      (abs_add_le _ _).trans (add_le_add h1 (h2.trans hpow))
    calc
      |(a - b) * a ^ k + b * (a ^ k - b ^ k)|
          ≤ |a - b| * R ^ k + (k : ℝ) * R ^ k * |a - b| := hsum
      _ = ((k + 1 : ℕ) : ℝ) * R ^ ((k + 1) - 1) * |a - b| := by
            simp only [Nat.add_sub_cancel]
            push_cast
            ring

lemma P3aL_local_expansion (S : SpinLaw) (hS : IsGHS S) (p : ℕ) (hp : IsTypeP S p) :
    ∃ C m₀ : ℝ, 0 < C ∧ 0 < m₀ ∧ ∀ m : ℝ, |m| ≤ m₀ →
        |rateI S m - (tau S / 2) * m ^ 2 - kappa S p * m ^ (2 * p)| ≤ C * |m| ^ (2 * p + 2) := by
  have hp2 : 2 ≤ p := hp.1
  let v : ℝ := variance S
  have hvpos : 0 < v := P3aL_variance_pos S
  have htau_pos : 0 < tau S := P3aL_tau_pos S
  have htauv : tau S * v = 1 := P3aL_tau_mul_variance S
  let a : ℝ := -iteratedDeriv (2 * p) (phi S) 0 / ((2 * p)! : ℝ)
  have hkap : kappa S p = a * tau S ^ (2 * p) := by
    unfold kappa
    have hvne : v ≠ 0 := ne_of_gt hvpos
    have htau : tau S = 1 / v := by
      have : tau S * v = 1 := htauv
      field_simp [hvne] at this ⊢
      linarith
    rw [htau, div_pow, one_pow]
    dsimp [a, v]
    ring
  -- Taylor bound for phi up to degree 2*p + 1 (remainder order 2*p + 2)
  obtain ⟨C₁, hC₁0, hTphi⟩ := P3aL_taylor_bound_Icc (phi S) ((P3aL_phi_contDiff S).of_le le_top) (2 * p + 1)
  have hphiPoly : ∀ t : ℝ,
      (∑ k ∈ Finset.range (2 * p + 2), (iteratedDeriv k (phi S) 0 / (k ! : ℝ)) * t ^ k) =
        (v / 2) * t ^ 2 - a * t ^ (2 * p) := by
    intro t
    have hsplit : Finset.range (2 * p + 2) =
        insert 0 (insert 2 (insert (2 * p)
          ((Finset.range (2 * p + 2)).filter fun k => k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 2 * p))) := by
      ext k
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
      omega
    have h0ne2 : (0 : ℕ) ∉ insert 2 (insert (2 * p)
        ((Finset.range (2 * p + 2)).filter fun k => k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 2 * p)) := by
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
      omega
    have h2ne2p : (2 : ℕ) ∉ insert (2 * p)
        ((Finset.range (2 * p + 2)).filter fun k => k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 2 * p) := by
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
      omega
    have h2pne : (2 * p : ℕ) ∉
        ((Finset.range (2 * p + 2)).filter fun k => k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 2 * p) := by
      simp only [Finset.mem_filter]
      omega
    rw [hsplit, Finset.sum_insert h0ne2, Finset.sum_insert h2ne2p, Finset.sum_insert h2pne]
    have hrest : (∑ k ∈ (Finset.range (2 * p + 2)).filter (fun k => k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 2 * p),
        (iteratedDeriv k (phi S) 0 / (k ! : ℝ)) * t ^ k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hj2 : 2 ≤ j := by omega
        have hjp : j < p := by omega
        have hk0 : iteratedDeriv k (phi S) 0 = 0 := by
          rw [show k = 2 * j by omega]
          exact hp.2.1 j hj2 hjp
        rw [hk0]; ring
      · rw [hj, P3aL_iteratedDeriv_odd_zero S j]; ring
    rw [hrest, add_zero, iteratedDeriv_zero, P3aL_phi_zero, P3aL_iteratedDeriv_two_zero S]
    norm_num [Nat.factorial]
    dsimp [a, v]
    ring
  have hphi_bound : ∀ t : ℝ, |t| ≤ 1 →
      |phi S t - ((v / 2) * t ^ 2 - a * t ^ (2 * p))| ≤ C₁ * |t| ^ (2 * p + 2) := by
    intro t ht
    rw [← hphiPoly t]
    exact hTphi t ht
  -- Taylor bound for deriv (phi S) up to degree 2*p - 2 (remainder order 2*p - 1)
  have hd_contDiff : ContDiff ℝ (⊤ : ℕ∞) (deriv (phi S)) := by
    have h1 : deriv (phi S) = iteratedDeriv 1 (phi S) := by rw [iteratedDeriv_one]
    rw [h1]
    exact P3aL_contDiff_iteratedDeriv 1 (P3aL_phi_contDiff S)
  obtain ⟨C₂, hC₂0, hTdphi⟩ := P3aL_taylor_bound_Icc (deriv (phi S)) hd_contDiff (2 * p - 2)
  have hdPoly : ∀ t : ℝ,
      (∑ k ∈ Finset.range (2 * p - 2 + 1),
          (iteratedDeriv k (deriv (phi S)) 0 / (k ! : ℝ)) * t ^ k) = v * t := by
    intro t
    have hmem : 1 ∈ Finset.range (2 * p - 2 + 1) := by
      rw [Finset.mem_range]
      omega
    rw [← Finset.add_sum_erase _ _ hmem]
    have h1term : (iteratedDeriv 1 (deriv (phi S)) 0 / (1 ! : ℝ)) * t ^ 1 = v * t := by
      rw [← iteratedDeriv_succ', P3aL_iteratedDeriv_two_zero S]
      norm_num [v]
    have hrest : (∑ k ∈ (Finset.range (2 * p - 2 + 1)).erase 1,
        (iteratedDeriv k (deriv (phi S)) 0 / (k ! : ℝ)) * t ^ k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_erase, Finset.mem_range] at hk
      rw [← iteratedDeriv_succ']
      rcases Nat.even_or_odd (k + 1) with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hj0 : j ≠ 0 := by omega
        have hj1 : j ≠ 1 := by omega
        have hj2 : 2 ≤ j := by omega
        have hjp : j < p := by omega
        rw [show k + 1 = 2 * j by omega, hp.2.1 j hj2 hjp]
        ring
      · rw [hj, P3aL_iteratedDeriv_odd_zero S j]
        ring
    rw [h1term, hrest, add_zero]
  have hdphi_bound : ∀ t : ℝ, |t| ≤ 1 →
      |deriv (phi S) t - v * t| ≤ C₂ * |t| ^ (2 * p - 1) := by
    intro t ht
    have h := hTdphi t ht
    rw [hdPoly t, show 2 * p - 2 + 1 = 2 * p - 1 by omega] at h
    exact h
  -- Choose t₀ ∈ (0, 1] small enough that C₂ * t₀^(2p-2) ≤ v / 2
  let t₀ : ℝ := min 1 ((v / (2 * (C₂ + 1))) ^ (1 : ℕ))
  -- Actually simpler: if C₂ * t^(2p-2) ≤ C₂ * t (for |t| ≤ 1 and 2p-2 ≥ 2 ≥ 1!),
  -- we just need |t| ≤ min 1 (v / (2 * (C₂ + 1)))!
  let t1 : ℝ := min 1 (v / (2 * (C₂ + 1)))
  have ht1_pos : 0 < t1 := lt_min (by norm_num) (div_pos hvpos (by linarith))
  have ht1_le1 : t1 ≤ 1 := min_le_left _ _
  have ht1_le_v : t1 ≤ v / (2 * (C₂ + 1)) := min_le_right _ _
  have hderiv_lb : ∀ t : ℝ, |t| ≤ t1 → |deriv (phi S) t - v * t| ≤ (v / 2) * |t| := by
    intro t ht
    have ht_le1 : |t| ≤ 1 := ht.trans ht1_le1
    have hdb := hdphi_bound t ht_le1
    have hpow : |t| ^ (2 * p - 1) ≤ |t| ^ 2 := by
      have hge : 2 ≤ 2 * p - 1 := by omega
      exact pow_le_pow_of_le_one (abs_nonneg t) ht_le1 hge
    have hpow2 : |t| ^ 2 ≤ t1 * |t| := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right ht (abs_nonneg t)
    have hC2_le : C₂ * (t1 * |t|) ≤ (v / 2) * |t| := by
      have ht1_mul : C₂ * t1 ≤ v / 2 := by
        calc
          C₂ * t1 ≤ (C₂ + 1) * t1 := mul_le_mul_of_nonneg_right (by linarith) ht1_pos.le
          _ ≤ (C₂ + 1) * (v / (2 * (C₂ + 1))) := mul_le_mul_of_nonneg_left ht1_le_v (by linarith)
          _ = v / 2 := by field_simp [show C₂ + 1 ≠ 0 by linarith]
      calc
        C₂ * (t1 * |t|) = (C₂ * t1) * |t| := by ring
        _ ≤ (v / 2) * |t| := mul_le_mul_of_nonneg_right ht1_mul (abs_nonneg t)
    calc
      |deriv (phi S) t - v * t| ≤ C₂ * |t| ^ (2 * p - 1) := hdb
      _ ≤ C₂ * |t| ^ 2 := mul_le_mul_of_nonneg_left hpow hC₂0
      _ ≤ C₂ * (t1 * |t|) := mul_le_mul_of_nonneg_left hpow2 hC₂0
      _ ≤ (v / 2) * |t| := hC2_le
  let m₀ : ℝ := (v / 2) * t1
  have hm₀_pos : 0 < m₀ := mul_pos (div_pos hvpos (by norm_num)) ht1_pos
  have hd_t1_ge : m₀ ≤ deriv (phi S) t1 := by
    have h1 := hderiv_lb t1 (by rw [abs_of_pos ht1_pos])
    have h2 := (abs_le.mp h1).1
    rw [abs_of_pos ht1_pos] at h2
    dsimp [m₀]
    linarith
  have hd_neg_t1_le : deriv (phi S) (-t1) ≤ -m₀ := by
    have h1 := hderiv_lb (-t1) (by rw [abs_neg, abs_of_pos ht1_pos])
    have h2 := (abs_le.mp h1).2
    rw [abs_neg, abs_of_pos ht1_pos] at h2
    dsimp [m₀]
    linarith
  -- Bound constant C
  let K_R : ℝ := 1 + tau S * C₂
  let K_t : ℝ := 2 * tau S
  let C : ℝ := (C₁ + (tau S / 2) * C₂ ^ 2 +
      |a| * ((2 * p : ℝ) * K_R ^ (2 * p - 1) * (tau S * C₂))) * K_t ^ (2 * p + 2) + 1
  have hC_pos : 0 < C := by positivity
  refine ⟨C, m₀, hC_pos, hm₀_pos, fun m hm => ?_⟩
  have hmIcc : m ∈ Set.Icc (deriv (phi S) (-t1)) (deriv (phi S) t1) := by
    have hmabs := abs_le.mp hm
    exact ⟨hd_neg_t1_le.trans hmabs.1, hmabs.2.trans hd_t1_ge⟩
  have hcont : ContinuousOn (deriv (phi S)) (Set.Icc (-t1) t1) :=
    hd_contDiff.continuous.continuousOn
  obtain ⟨t, htIcc, htm⟩ := intermediate_value_Icc (by linarith : -t1 ≤ t1) hcont hmIcc
  have htabs : |t| ≤ t1 := abs_le.mpr htIcc
  have htle1 : |t| ≤ 1 := htabs.trans ht1_le1
  have hrate : rateI S m = t * m - phi S t := by
    rw [← htm]
    exact P3aL_rateI_at_deriv S t
  have hmt_lb : (v / 2) * |t| ≤ |m| := by
    have h1 := hderiv_lb t htabs
    rw [htm] at h1
    have htri : |v * t| - |m - v * t| ≤ |m| := by
      have h1' := abs_sub_abs_le_abs_sub (v * t) (v * t - m)
      have h2' : v * t - (v * t - m) = m := by ring
      have h3' : |v * t - m| = |m - v * t| := abs_sub_comm _ _
      rw [h2', h3'] at h1'
      exact h1'
    have hvt : |v * t| = v * |t| := by rw [abs_mul, abs_of_pos hvpos]
    linarith
  have htm_ub : |t| ≤ K_t * |m| := by
    dsimp [K_t]
    have hdiv : |t| ≤ (2 / v) * |m| := by
      have hvne : v ≠ 0 := ne_of_gt hvpos
      calc
        |t| = (2 / v) * ((v / 2) * |t|) := by field_simp [hvne]
        _ ≤ (2 / v) * |m| := by gcongr
    have h2tau : 2 / v = 2 * tau S := by
      have hvne : v ≠ 0 := ne_of_gt hvpos
      calc
        2 / v = 2 * (1 / v) := by ring
        _ = 2 * (tau S * v / v) := by rw [htauv]
        _ = 2 * tau S := by field_simp [hvne]
    rwa [h2tau] at hdiv
  let δ : ℝ := m - v * t
  have hδ_bound : |δ| ≤ C₂ * |t| ^ (2 * p - 1) := by
    dsimp [δ]
    rw [← htm]
    exact hdphi_bound t htle1
  let r₁ : ℝ := phi S t - ((v / 2) * t ^ 2 - a * t ^ (2 * p))
  have hr₁_bound : |r₁| ≤ C₁ * |t| ^ (2 * p + 2) := hphi_bound t htle1
  have hid : rateI S m - (tau S / 2) * m ^ 2 - kappa S p * m ^ (2 * p) =
      -r₁ - (tau S / 2) * δ ^ 2 + a * (t ^ (2 * p) - (tau S * m) ^ (2 * p)) := by
    rw [hrate, hkap]
    have hm_eq : m = v * t + δ := by dsimp [δ]; ring
    have hphi_eq : phi S t = (v / 2) * t ^ 2 - a * t ^ (2 * p) + r₁ := by dsimp [r₁]; ring
    have htaum : (tau S * m) ^ (2 * p) = tau S ^ (2 * p) * m ^ (2 * p) := mul_pow _ _ _
    rw [htaum, hm_eq, hphi_eq]
    have hquad : (tau S / 2) * (v * t + δ) ^ 2 =
        (tau S * v) * (v / 2) * t ^ 2 + (tau S * v) * t * δ + (tau S / 2) * δ ^ 2 := by ring
    rw [hquad, htauv]
    ring
  have hδ_pow_bound : |δ| ^ 2 ≤ C₂ ^ 2 * |t| ^ (2 * p + 2) := by
    have h1 : |δ| ^ 2 ≤ (C₂ * |t| ^ (2 * p - 1)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg δ) hδ_bound 2
    have h2 : (C₂ * |t| ^ (2 * p - 1)) ^ 2 = C₂ ^ 2 * |t| ^ (2 * (2 * p - 1)) := by
      rw [mul_pow, ← pow_mul]
      ring_nf
    have h3 : |t| ^ (2 * (2 * p - 1)) ≤ |t| ^ (2 * p + 2) := by
      have hexp : 2 * p + 2 ≤ 2 * (2 * p - 1) := by omega
      exact pow_le_pow_of_le_one (abs_nonneg t) htle1 hexp
    calc
      |δ| ^ 2 ≤ C₂ ^ 2 * |t| ^ (2 * (2 * p - 1)) := h1.trans_eq h2
      _ ≤ C₂ ^ 2 * |t| ^ (2 * p + 2) := mul_le_mul_of_nonneg_left h3 (sq_nonneg C₂)
  have htau_m_bound : |tau S * m| ≤ K_R * |t| := by
    have heq : tau S * m = t + tau S * δ := by
      calc
        tau S * m = tau S * (v * t + δ) := by dsimp [δ]; ring
        _ = (tau S * v) * t + tau S * δ := by ring
        _ = t + tau S * δ := by rw [htauv, one_mul]
    have hδle : |δ| ≤ C₂ * |t| := by
      have hexp : 1 ≤ 2 * p - 1 := by omega
      have hpow : |t| ^ (2 * p - 1) ≤ |t| ^ 1 := pow_le_pow_of_le_one (abs_nonneg t) htle1 hexp
      simpa using hδ_bound.trans (mul_le_mul_of_nonneg_left hpow hC₂0)
    calc
      |tau S * m| = |t + tau S * δ| := by rw [heq]
      _ ≤ |t| + |tau S * δ| := abs_add_le _ _
      _ = |t| + tau S * |δ| := by rw [abs_mul, abs_of_pos htau_pos]
      _ ≤ |t| + tau S * (C₂ * |t|) := by gcongr
      _ = K_R * |t| := by dsimp [K_R]; ring
  have ht_le_KR : |t| ≤ K_R * |t| := by
    have hKR1 : 1 ≤ K_R := by dsimp [K_R]; linarith [mul_nonneg htau_pos.le hC₂0]
    exact le_mul_of_one_le_left (abs_nonneg t) hKR1
  have hpow_diff : |t ^ (2 * p) - (tau S * m) ^ (2 * p)| ≤
      ((2 * p : ℝ) * K_R ^ (2 * p - 1) * (tau S * C₂)) * |t| ^ (2 * p + 2) := by
    have hdiff := P3aL_abs_pow_sub_le (2 * p) t (tau S * m) (K_R * |t|) ht_le_KR htau_m_bound
    have hsub : |t - tau S * m| = tau S * |δ| := by
      have heq : t - tau S * m = -(tau S * δ) := by
        calc
          t - tau S * m = t - tau S * (v * t + δ) := by dsimp [δ]; ring
          _ = (1 - tau S * v) * t - tau S * δ := by ring
          _ = -(tau S * δ) := by rw [htauv]; ring
      rw [heq, abs_neg, abs_mul, abs_of_pos htau_pos]
    have hpow_exp : |t| ^ (2 * p - 1) * |t| ^ (2 * p - 1) ≤ |t| ^ (2 * p + 2) := by
      rw [← pow_add]
      have hexp : 2 * p + 2 ≤ (2 * p - 1) + (2 * p - 1) := by omega
      exact pow_le_pow_of_le_one (abs_nonneg t) htle1 hexp
    calc
      |t ^ (2 * p) - (tau S * m) ^ (2 * p)|
          ≤ ((2 * p : ℕ) : ℝ) * (K_R * |t|) ^ (2 * p - 1) * |t - tau S * m| := hdiff
      _ = (2 * p : ℝ) * K_R ^ (2 * p - 1) * |t| ^ (2 * p - 1) * (tau S * |δ|) := by
            push_cast; rw [hsub, mul_pow]; ring
      _ ≤ (2 * p : ℝ) * K_R ^ (2 * p - 1) * |t| ^ (2 * p - 1) * (tau S * (C₂ * |t| ^ (2 * p - 1))) := by
            gcongr
      _ = ((2 * p : ℝ) * K_R ^ (2 * p - 1) * (tau S * C₂)) * (|t| ^ (2 * p - 1) * |t| ^ (2 * p - 1)) := by
            ring
      _ ≤ ((2 * p : ℝ) * K_R ^ (2 * p - 1) * (tau S * C₂)) * |t| ^ (2 * p + 2) := by
            gcongr
  have htri_all : |rateI S m - (tau S / 2) * m ^ 2 - kappa S p * m ^ (2 * p)| ≤
      |r₁| + (tau S / 2) * |δ| ^ 2 + |a| * |t ^ (2 * p) - (tau S * m) ^ (2 * p)| := by
    rw [hid]
    have h1 : |-r₁ - (tau S / 2) * δ ^ 2 + a * (t ^ (2 * p) - (tau S * m) ^ (2 * p))| ≤
        |-r₁ - (tau S / 2) * δ ^ 2| + |a * (t ^ (2 * p) - (tau S * m) ^ (2 * p))| := abs_add_le _ _
    have h2 : |-r₁ - (tau S / 2) * δ ^ 2| ≤ |-r₁| + |(tau S / 2) * δ ^ 2| := abs_sub _ _
    have h3 : |-r₁| = |r₁| := abs_neg r₁
    have h4 : |(tau S / 2) * δ ^ 2| = (tau S / 2) * |δ| ^ 2 := by
      rw [abs_mul, abs_of_pos (div_pos htau_pos (by norm_num)), abs_sq, sq_abs]
    have h5 : |a * (t ^ (2 * p) - (tau S * m) ^ (2 * p))| =
        |a| * |t ^ (2 * p) - (tau S * m) ^ (2 * p)| := abs_mul _ _
    linarith
  have ht_pow_m : |t| ^ (2 * p + 2) ≤ (K_t ^ (2 * p + 2)) * |m| ^ (2 * p + 2) := by
    calc
      |t| ^ (2 * p + 2) ≤ (K_t * |m|) ^ (2 * p + 2) :=
        pow_le_pow_left₀ (abs_nonneg t) htm_ub (2 * p + 2)
      _ = K_t ^ (2 * p + 2) * |m| ^ (2 * p + 2) := mul_pow _ _ _
  calc
    |rateI S m - (tau S / 2) * m ^ 2 - kappa S p * m ^ (2 * p)|
        ≤ |r₁| + (tau S / 2) * |δ| ^ 2 + |a| * |t ^ (2 * p) - (tau S * m) ^ (2 * p)| := htri_all
    _ ≤ C₁ * |t| ^ (2 * p + 2) + (tau S / 2) * (C₂ ^ 2 * |t| ^ (2 * p + 2)) +
          |a| * (((2 * p : ℝ) * K_R ^ (2 * p - 1) * (tau S * C₂)) * |t| ^ (2 * p + 2)) := by
          gcongr
    _ = (C₁ + (tau S / 2) * C₂ ^ 2 +
          |a| * ((2 * p : ℝ) * K_R ^ (2 * p - 1) * (tau S * C₂))) * |t| ^ (2 * p + 2) := by ring
    _ ≤ (C₁ + (tau S / 2) * C₂ ^ 2 +
          |a| * ((2 * p : ℝ) * K_R ^ (2 * p - 1) * (tau S * C₂))) *
            (K_t ^ (2 * p + 2) * |m| ^ (2 * p + 2)) := by
          gcongr
    _ ≤ C * |m| ^ (2 * p + 2) := by
          dsimp [C]
          have hpowm : 0 ≤ |m| ^ (2 * p + 2) := by positivity
          nlinarith

end CritWinSpin

open CritWinSpin

/-- Lemma 3.1(i), the local expansion (1). -/
theorem solution (S : SpinLaw) (hS : IsGHS S) (p : ℕ) (hp : IsTypeP S p) :
    ∃ C m₀ : ℝ, 0 < C ∧ 0 < m₀ ∧ ∀ m : ℝ, |m| ≤ m₀ →
        |rateI S m - (tau S / 2) * m ^ 2 - kappa S p * m ^ (2 * p)| ≤ C * |m| ^ (2 * p + 2) :=
  P3aL_local_expansion S hS p hp
