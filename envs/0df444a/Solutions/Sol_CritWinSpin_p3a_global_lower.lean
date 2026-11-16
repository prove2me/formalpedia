-- Prove2me | solution 1 for CritWinSpin.p3a_global_lower
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-15T22:36:41.688279+00:00
-- url     : https://prove2.me/submissions/099b1f58-333e-443b-abb4-dfd44009a041

import Mathlib
import Definitions.Def_CritWinSpin_SpinLaw
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
open scoped BigOperators Nat

namespace CritWinSpin

noncomputable def P3aG_Z (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))

noncomputable def P3aG_Z1 (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))

noncomputable def P3aG_Z2 (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))

lemma P3aG_Z_pos (S : SpinLaw) (t : ℝ) : 0 < P3aG_Z S t := by
  unfold P3aG_Z
  apply Finset.sum_pos'
  · intro x hx
    exact mul_nonneg (by exact_mod_cast (le_of_lt (S.pos x hx))) (Real.exp_pos _).le
  · refine ⟨1, S.one_mem, ?_⟩
    exact mul_pos (by exact_mod_cast S.pos 1 S.one_mem) (Real.exp_pos _)

lemma P3aG_Z_zero (S : SpinLaw) : P3aG_Z S 0 = 1 := by
  unfold P3aG_Z
  simp only [zero_mul, Real.exp_zero, mul_one]
  exact_mod_cast S.sum_one

lemma P3aG_variance_pos (S : SpinLaw) : 0 < variance S := by
  have hvQ : 0 < varQ S := by
    have h1 : 0 < (1 : ℚ) ^ 2 * S.ρ 1 := by simpa using S.pos 1 S.one_mem
    have hnonneg : ∀ x ∈ S.A, 0 ≤ x ^ 2 * S.ρ x := fun x hx =>
      mul_nonneg (sq_nonneg x) (S.pos x hx).le
    have hle : (1 : ℚ) ^ 2 * S.ρ 1 ≤ varQ S := by
      rw [varQ]
      exact Finset.single_le_sum hnonneg S.one_mem
    exact lt_of_lt_of_le h1 hle
  exact Rat.cast_pos.mpr hvQ

lemma P3aG_tau_mul_variance (S : SpinLaw) : tau S * variance S = 1 := by
  have hvpos : 0 < variance S := P3aG_variance_pos S
  have hvne : variance S ≠ 0 := ne_of_gt hvpos
  have htau : tau S = 1 / variance S := by
    unfold tau tauQ variance
    push_cast
    rfl
  rw [htau]
  field_simp [hvne]

lemma P3aG_tau_pos (S : SpinLaw) : 0 < tau S := by
  have h1 := P3aG_tau_mul_variance S
  have hv := P3aG_variance_pos S
  nlinarith

lemma P3aG_Z1_zero (S : SpinLaw) : P3aG_Z1 S 0 = 0 := by
  unfold P3aG_Z1
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

lemma P3aG_Z2_zero (S : SpinLaw) : P3aG_Z2 S 0 = variance S := by
  unfold P3aG_Z2 variance varQ
  simp only [zero_mul, Real.exp_zero, mul_one]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma P3aG_hasDerivAt_Z (S : SpinLaw) (t : ℝ) : HasDerivAt (P3aG_Z S) (P3aG_Z1 S t) t := by
  unfold P3aG_Z P3aG_Z1
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

lemma P3aG_hasDerivAt_Z1 (S : SpinLaw) (t : ℝ) : HasDerivAt (P3aG_Z1 S) (P3aG_Z2 S t) t := by
  unfold P3aG_Z1 P3aG_Z2
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

lemma P3aG_hasDerivAt_phi (S : SpinLaw) (t : ℝ) :
    HasDerivAt (phi S) (P3aG_Z1 S t / P3aG_Z S t) t := by
  change HasDerivAt (fun s => Real.log (P3aG_Z S s)) (P3aG_Z1 S t / P3aG_Z S t) t
  exact (P3aG_hasDerivAt_Z S t).log (ne_of_gt (P3aG_Z_pos S t))

lemma P3aG_deriv_phi (S : SpinLaw) : deriv (phi S) = fun t => P3aG_Z1 S t / P3aG_Z S t := by
  funext t
  exact (P3aG_hasDerivAt_phi S t).deriv

lemma P3aG_phi_analyticOnNhd (S : SpinLaw) : AnalyticOnNhd ℝ (phi S) Set.univ := by
  intro t _
  change AnalyticAt ℝ (fun s => Real.log (P3aG_Z S s)) t
  have hZ : AnalyticAt ℝ (P3aG_Z S) t := by
    unfold P3aG_Z
    refine Finset.analyticAt_fun_sum S.A fun x _ => ?_
    exact analyticAt_const.mul (analyticAt_rexp.comp ((analyticAt_id : AnalyticAt ℝ id t).mul analyticAt_const))
  exact (analyticAt_log (P3aG_Z_pos S t)).comp hZ

lemma P3aG_phi_contDiff (S : SpinLaw) : ContDiff ℝ ⊤ (phi S) :=
  (P3aG_phi_analyticOnNhd S).contDiff

lemma P3aG_phi_zero (S : SpinLaw) : phi S 0 = 0 := by
  change Real.log (P3aG_Z S 0) = 0
  rw [P3aG_Z_zero, Real.log_one]

lemma P3aG_iteratedDeriv_one_zero (S : SpinLaw) : iteratedDeriv 1 (phi S) 0 = 0 := by
  rw [iteratedDeriv_one, P3aG_deriv_phi]
  dsimp only
  rw [P3aG_Z1_zero, P3aG_Z_zero]
  norm_num

lemma P3aG_iteratedDeriv_two_zero (S : SpinLaw) : iteratedDeriv 2 (phi S) 0 = variance S := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, P3aG_deriv_phi]
  have hd := (P3aG_hasDerivAt_Z1 S 0).div (P3aG_hasDerivAt_Z S 0) (ne_of_gt (P3aG_Z_pos S 0))
  change HasDerivAt (fun t => P3aG_Z1 S t / P3aG_Z S t) _ 0 at hd
  rw [hd.deriv, P3aG_Z2_zero, P3aG_Z_zero, P3aG_Z1_zero]
  norm_num

lemma P3aG_phi_even (S : SpinLaw) (t : ℝ) : phi S (-t) = phi S t := by
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

lemma P3aG_iteratedDeriv_even_symm (S : SpinLaw) (n : ℕ) :
    ∀ t : ℝ, iteratedDeriv n (phi S) (-t) = (-1 : ℝ) ^ n * iteratedDeriv n (phi S) t := by
  induction n with
  | zero => intro t; simp [P3aG_phi_even S t]
  | succ n ih =>
    intro t
    have hdiff : Differentiable ℝ (iteratedDeriv n (phi S)) :=
      (P3aG_phi_contDiff S).differentiable_iteratedDeriv n
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

lemma P3aG_iteratedDeriv_odd_zero (S : SpinLaw) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (phi S) 0 = 0 := by
  have h := P3aG_iteratedDeriv_even_symm S (2 * k + 1) 0
  simp only [neg_zero] at h
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
  rw [hpow] at h
  linarith

lemma P3aG_quad_iteratedDeriv (c : ℝ) :
    (∀ n : ℕ, 3 ≤ n → iteratedDeriv n (fun t : ℝ => c * t ^ 2) 0 = 0) ∧
    iteratedDeriv 0 (fun t : ℝ => c * t ^ 2) 0 = 0 ∧
    iteratedDeriv 1 (fun t : ℝ => c * t ^ 2) 0 = 0 ∧
    iteratedDeriv 2 (fun t : ℝ => c * t ^ 2) 0 = 2 * c := by
  have hd1 : deriv (fun t : ℝ => c * t ^ 2) = fun t => 2 * c * t := by
    funext t
    have h0 := ((hasDerivAt_id' t).pow 2).const_mul c
    rw [show c * ((2 : ℕ) * t ^ (2 - 1) * 1) = 2 * c * t by norm_num; ring] at h0
    exact h0.deriv
  have hd2 : deriv (fun t : ℝ => 2 * c * t) = fun _ => 2 * c := by
    funext t
    have h0 := (hasDerivAt_id' t).const_mul (2 * c)
    rw [mul_one] at h0
    exact h0.deriv
  have hd3 : deriv (fun _ : ℝ => (2 * c : ℝ)) = fun _ => 0 := by
    funext t
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [show m + 3 = (m + 1) + 2 from by ring]
    rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', hd1, hd2, hd3]
    simp [iteratedDeriv_fun_const_zero]
  · simp
  · rw [iteratedDeriv_one, hd1]; simp
  · rw [iteratedDeriv_succ', iteratedDeriv_one, hd1, hd2]

lemma P3aG_rateI_bddAbove (S : SpinLaw) (m : ℝ) (hm : |m| ≤ 1) :
    BddAbove (Set.range fun t : ℝ => t * m - phi S t) := by
  refine ⟨-Real.log (S.ρ 1 : ℝ), ?_⟩
  rintro _ ⟨t, rfl⟩
  have h1pos : (0 : ℝ) < (S.ρ 1 : ℝ) := by exact_mod_cast S.pos 1 S.one_mem
  have hm1pos : (0 : ℝ) < (S.ρ (-1) : ℝ) := by exact_mod_cast S.pos (-1) S.neg_one_mem
  have hZge : (S.ρ 1 : ℝ) * Real.exp |t| ≤ P3aG_Z S t := by
    unfold P3aG_Z
    have hnonneg : ∀ x ∈ S.A, 0 ≤ (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := fun x hx =>
      mul_nonneg (by exact_mod_cast (S.pos x hx).le) (Real.exp_pos _).le
    rcases le_total 0 t with ht0 | ht0
    · rw [abs_of_nonneg ht0]
      have hterm : (S.ρ 1 : ℝ) * Real.exp t = (S.ρ (1 : ℚ) : ℝ) * Real.exp (t * ((1 : ℚ) : ℝ)) := by
        simp
      rw [hterm]
      exact Finset.single_le_sum hnonneg S.one_mem
    · rw [abs_of_nonpos ht0]
      have hterm : (S.ρ 1 : ℝ) * Real.exp (-t) =
          (S.ρ (-1 : ℚ) : ℝ) * Real.exp (t * ((-1 : ℚ) : ℝ)) := by
        rw [S.symm 1 S.one_mem]
        simp
      rw [hterm]
      exact Finset.single_le_sum hnonneg S.neg_one_mem
  have hlog : Real.log (S.ρ 1 : ℝ) + |t| ≤ phi S t := by
    have hmulpos : 0 < (S.ρ 1 : ℝ) * Real.exp |t| := mul_pos h1pos (Real.exp_pos _)
    have h1 := Real.log_le_log hmulpos hZge
    rw [Real.log_mul (ne_of_gt h1pos) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h1
    exact h1
  have htm : t * m ≤ |t| := by
    calc
      t * m ≤ |t * m| := le_abs_self _
      _ = |t| * |m| := abs_mul t m
      _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hm (abs_nonneg t)
      _ = |t| := mul_one _
  linarith

lemma P3aG_rateI_even (S : SpinLaw) (m : ℝ) (hm : |m| ≤ 1) : rateI S (-m) = rateI S m := by
  have hm_neg : |-m| ≤ 1 := by simpa [abs_neg] using hm
  have hbdd1 := P3aG_rateI_bddAbove S (-m) hm_neg
  have hbdd2 := P3aG_rateI_bddAbove S m hm
  unfold rateI
  apply le_antisymm
  · refine ciSup_le fun t => ?_
    have heq : t * (-m) - phi S t = (-t) * m - phi S (-t) := by
      rw [P3aG_phi_even]
      ring
    rw [heq]
    exact le_ciSup hbdd2 (-t)
  · refine ciSup_le fun t => ?_
    have heq : t * m - phi S t = (-t) * (-m) - phi S (-t) := by
      rw [P3aG_phi_even]
      ring
    rw [heq]
    exact le_ciSup hbdd1 (-t)

lemma P3aG_global_lower (S : SpinLaw) (hS : IsGHS S) (p : ℕ) (hp : IsTypeP S p) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, |m| ≤ 1 →
        (tau S / 2) * m ^ 2 + c * m ^ (2 * p) ≤ rateI S m := by
  have hp2 : 2 ≤ p := hp.1
  have hpmin : ∀ j : ℕ, 2 ≤ j → j < p → iteratedDeriv (2 * j) (phi S) 0 = 0 := hp.2.1
  have hpneg : iteratedDeriv (2 * p) (phi S) 0 < 0 := hp.2.2
  let v : ℝ := variance S
  have hvpos : 0 < v := P3aG_variance_pos S
  have htau_pos : 0 < tau S := P3aG_tau_pos S
  have htauv : tau S * v = 1 := P3aG_tau_mul_variance S
  let g : ℝ → ℝ := fun t => (v / 2) * t ^ 2 - phi S t
  have hg_contDiff : ContDiff ℝ ⊤ g := by
    have hq : ContDiff ℝ ⊤ (fun t : ℝ => (v / 2) * t ^ 2) := by fun_prop
    exact hq.sub (P3aG_phi_contDiff S)
  have hphi_d2_anti : AntitoneOn (iteratedDeriv 2 (phi S)) (Set.Ici 0) := by
    have hd2_diff : Differentiable ℝ (iteratedDeriv 2 (phi S)) :=
      (P3aG_phi_contDiff S).differentiable_iteratedDeriv 2
        (by exact_mod_cast (WithTop.coe_lt_top (2 : ℕ∞) : ((2 : ℕ∞) : WithTop ℕ∞) < ⊤))
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact hd2_diff.continuous.continuousOn
    · exact hd2_diff.differentiableOn
    · intro t ht
      rw [← iteratedDeriv_succ]
      exact hS t (interior_Ici.subset ht).le
  have hg_mono : MonotoneOn g (Set.Ici 0) := by
    have hg_diff : Differentiable ℝ g := hg_contDiff.differentiable (by simp)
    have hgp_diff : Differentiable ℝ (deriv g) := by
      have : deriv g = iteratedDeriv 1 g := (iteratedDeriv_one).symm
      rw [this]
      exact hg_contDiff.differentiable_iteratedDeriv 1
        (by exact_mod_cast (WithTop.coe_lt_top (1 : ℕ∞) : ((1 : ℕ∞) : WithTop ℕ∞) < ⊤))
    have hgp_eq : ∀ t : ℝ, deriv g t = v * t - deriv (phi S) t := by
      intro t
      have hd1 : HasDerivAt (fun s : ℝ => (v / 2) * s ^ 2) (v * t) t := by
        have h0 := ((hasDerivAt_id' t).pow 2).const_mul (v / 2)
        rw [show (v / 2) * ((2 : ℕ) * t ^ (2 - 1) * 1) = v * t by norm_num; ring] at h0
        exact h0
      have hd2 : HasDerivAt (phi S) (deriv (phi S) t) t := by
        rw [P3aG_deriv_phi]
        exact P3aG_hasDerivAt_phi S t
      exact (hd1.sub hd2).deriv
    have hgp_mono : MonotoneOn (deriv g) (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact hgp_diff.continuous.continuousOn
      · exact hgp_diff.differentiableOn
      · intro t ht
        have ht0 : (0 : ℝ) ≤ t := (interior_Ici.subset ht).le
        have hd_eq : deriv g = fun s => v * s - deriv (phi S) s := funext hgp_eq
        have hd_gp : HasDerivAt (deriv g) (v - iteratedDeriv 2 (phi S) t) t := by
          rw [hd_eq]
          have hd_lin : HasDerivAt (fun s : ℝ => v * s) v t := by
            have h0 := (hasDerivAt_id' t).const_mul v
            rw [mul_one] at h0
            exact h0
          have hd_phi' : HasDerivAt (deriv (phi S)) (iteratedDeriv 2 (phi S) t) t := by
            rw [iteratedDeriv_succ, iteratedDeriv_one]
            have hd' : Differentiable ℝ (deriv (phi S)) := by
              rw [← iteratedDeriv_one]
              exact (P3aG_phi_contDiff S).differentiable_iteratedDeriv 1
                (by exact_mod_cast (WithTop.coe_lt_top (1 : ℕ∞) : ((1 : ℕ∞) : WithTop ℕ∞) < ⊤))
            exact (hd' t).hasDerivAt
          exact hd_lin.sub hd_phi'
        rw [hd_gp.deriv]
        have hle : iteratedDeriv 2 (phi S) t ≤ iteratedDeriv 2 (phi S) 0 :=
          hphi_d2_anti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht0) ht0
        rw [P3aG_iteratedDeriv_two_zero] at hle
        linarith
    have hgp0 : deriv g 0 = 0 := by
      rw [hgp_eq 0, mul_zero, ← iteratedDeriv_one, P3aG_iteratedDeriv_one_zero, sub_zero]
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact hg_diff.continuous.continuousOn
    · exact hg_diff.differentiableOn
    · intro t ht
      have ht0 : (0 : ℝ) ≤ t := (interior_Ici.subset ht).le
      have hge := hgp_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht0) ht0
      linarith
  have hg_zero_derivs : ∀ k : ℕ, k < 2 * p → iteratedDeriv k g 0 = 0 := by
    intro k hk
    have hq_cd : ContDiff ℝ ⊤ (fun t : ℝ => (v / 2) * t ^ 2) := by fun_prop
    have hsub : iteratedDeriv k g 0 =
        iteratedDeriv k (fun t : ℝ => (v / 2) * t ^ 2) 0 - iteratedDeriv k (phi S) 0 := by
      change iteratedDeriv k ((fun t : ℝ => (v / 2) * t ^ 2) - phi S) 0 = _
      exact iteratedDeriv_fun_sub (hq_cd.contDiffAt.of_le le_top)
        ((P3aG_phi_contDiff S).contDiffAt.of_le le_top)
    rw [hsub]
    have hqd := P3aG_quad_iteratedDeriv (v / 2)
    rcases lt_trichotomy k 2 with hk2 | rfl | hk2
    · interval_cases k
      · simp [iteratedDeriv_zero, P3aG_phi_zero]
      · rw [hqd.2.2.1, P3aG_iteratedDeriv_one_zero, sub_zero]
    · rw [hqd.2.2.2, P3aG_iteratedDeriv_two_zero]; dsimp [v]; ring
    · rw [hqd.1 k hk2, zero_sub, neg_eq_zero]
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hj2 : 2 ≤ j := by omega
        have hjp : j < p := by omega
        rw [show k = 2 * j from by omega]
        exact hpmin j hj2 hjp
      · rw [hj]
        exact P3aG_iteratedDeriv_odd_zero S j
  have hg_2p_pos : 0 < iteratedDeriv (2 * p) g 0 := by
    have hq_cd : ContDiff ℝ ⊤ (fun t : ℝ => (v / 2) * t ^ 2) := by fun_prop
    have hsub : iteratedDeriv (2 * p) g 0 =
        iteratedDeriv (2 * p) (fun t : ℝ => (v / 2) * t ^ 2) 0 -
          iteratedDeriv (2 * p) (phi S) 0 := by
      change iteratedDeriv (2 * p) ((fun t : ℝ => (v / 2) * t ^ 2) - phi S) 0 = _
      exact iteratedDeriv_fun_sub (hq_cd.contDiffAt.of_le le_top)
        ((P3aG_phi_contDiff S).contDiffAt.of_le le_top)
    have hqd := P3aG_quad_iteratedDeriv (v / 2)
    rw [hsub, hqd.1 (2 * p) (by omega), zero_sub]
    linarith
  let L : ℝ := iteratedDeriv (2 * p) g 0
  have hLpos : 0 < L := hg_2p_pos
  have hcont_2p : Continuous (iteratedDeriv (2 * p) g) :=
    hg_contDiff.continuous_iteratedDeriv (2 * p) le_top
  have hnhds : ∀ᶠ x in nhds (0 : ℝ), L / 2 < iteratedDeriv (2 * p) g x :=
    hcont_2p.continuousAt.eventually (Ioi_mem_nhds (by linarith : L / 2 < L))
  obtain ⟨δ, hδpos, hδball⟩ := Metric.eventually_nhds_iff.mp hnhds
  let a : ℝ := L / (2 * ((2 * p)! : ℝ))
  have hapos : 0 < a := by positivity
  have hg_local : ∀ t : ℝ, 0 ≤ t → t ≤ δ / 2 → a * t ^ (2 * p) ≤ g t := by
    intro t ht0 htle
    rcases eq_or_lt_of_le ht0 with rfl | htpos
    · have hpow0 : (0 : ℝ) ^ (2 * p) = 0 := zero_pow (by omega)
      have hg0 : g 0 = 0 := by dsimp [g]; rw [P3aG_phi_zero]; ring
      rw [hpow0, mul_zero, hg0]
    · have htne : (0 : ℝ) ≠ t := ne_of_lt htpos
      have hm1 : (2 * p - 1) + 1 = 2 * p := by omega
      have hgC : ContDiffOn ℝ ((2 * p - 1) + 1) g (Set.uIcc 0 t) :=
        (hg_contDiff.of_le le_top).contDiffOn
      obtain ⟨x', hx'mem, hx'eq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv htne hgC
      have htay0 : taylorWithinEval g (2 * p - 1) (Set.uIcc 0 t) 0 t = 0 := by
        rw [taylor_within_apply]
        apply Finset.sum_eq_zero
        intro k hk
        have hlt : k < 2 * p := by
          have := Finset.mem_range.mp hk
          omega
        have hu : UniqueDiffOn ℝ (Set.uIcc 0 t) := uniqueDiffOn_uIcc htne
        have hwithin : iteratedDerivWithin k g (Set.uIcc 0 t) 0 = iteratedDeriv k g 0 :=
          iteratedDerivWithin_eq_iteratedDeriv hu
            ((hg_contDiff.of_le le_top).contDiffAt) Set.left_mem_uIcc
        rw [hwithin, hg_zero_derivs k hlt, smul_zero]
      rw [htay0, sub_zero, hm1] at hx'eq
      have hx'Ioo : x' ∈ Set.Ioo 0 t := by
        simpa [Set.uIoo_of_lt htpos] using hx'mem
      have hx'dist : dist x' 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hx'Ioo.1]
        linarith [hx'Ioo.2]
      have hx'gt : L / 2 < iteratedDeriv (2 * p) g x' := hδball hx'dist
      rw [hx'eq, sub_zero]
      have hfact_pos : (0 : ℝ) < ((2 * p)! : ℝ) := by positivity
      have ht_pow_nn : 0 ≤ t ^ (2 * p) := pow_nonneg ht0 (2 * p)
      calc
        a * t ^ (2 * p) = (L / 2) * t ^ (2 * p) / ((2 * p)! : ℝ) := by
          dsimp [a]; ring
        _ ≤ iteratedDeriv (2 * p) g x' * t ^ (2 * p) / ((2 * p)! : ℝ) := by
          gcongr
  let m₁ : ℝ := min 1 (δ / (2 * tau S))
  have hm₁_pos : 0 < m₁ := lt_min (by norm_num) (div_pos hδpos (by linarith))
  have hm₁_le1 : m₁ ≤ 1 := min_le_left _ _
  have hm₁_leδ : tau S * m₁ ≤ δ / 2 := by
    have h1 : m₁ ≤ δ / (2 * tau S) := min_le_right _ _
    have h2 : tau S * m₁ ≤ tau S * (δ / (2 * tau S)) :=
      mul_le_mul_of_nonneg_left h1 htau_pos.le
    have htau_ne : tau S ≠ 0 := ne_of_gt htau_pos
    calc
      tau S * m₁ ≤ tau S * (δ / (2 * tau S)) := h2
      _ = δ / 2 := by field_simp [htau_ne]
  let c : ℝ := a * (tau S * m₁) ^ (2 * p)
  have hc_pos : 0 < c := by positivity
  refine ⟨c, hc_pos, fun m hm => ?_⟩
  have hnonneg_case : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      (tau S / 2) * x ^ 2 + c * x ^ (2 * p) ≤ rateI S x := by
    intro x hx0 hx1
    have hxabs : |x| ≤ 1 := abs_le.mpr ⟨by linarith, hx1⟩
    let t : ℝ := tau S * x
    have hle_rate : t * x - phi S t ≤ rateI S x := by
      unfold rateI
      exact le_ciSup (P3aG_rateI_bddAbove S x hxabs) t
    have hid : t * x - phi S t = (tau S / 2) * x ^ 2 + g t := by
      dsimp [g, t]
      have hquad : (v / 2) * (tau S * x) ^ 2 = (tau S * v) * (tau S / 2) * x ^ 2 := by ring
      rw [hquad, htauv]
      ring
    have hcg : c * x ^ (2 * p) ≤ g t := by
      rcases le_or_gt x m₁ with hxm | hmx
      · have ht0 : 0 ≤ t := mul_nonneg htau_pos.le hx0
        have htle : t ≤ δ / 2 := by
          calc
            t = tau S * x := rfl
            _ ≤ tau S * m₁ := mul_le_mul_of_nonneg_left hxm htau_pos.le
            _ ≤ δ / 2 := hm₁_leδ
        have hloc := hg_local t ht0 htle
        have hm1_pow : m₁ ^ (2 * p) ≤ 1 := pow_le_one₀ hm₁_pos.le hm₁_le1
        have hpowx : 0 ≤ x ^ (2 * p) := pow_nonneg hx0 (2 * p)
        calc
          c * x ^ (2 * p) = a * (tau S * x) ^ (2 * p) * m₁ ^ (2 * p) := by
            dsimp [c]; rw [mul_pow]; ring
          _ ≤ a * (tau S * x) ^ (2 * p) * 1 := by
            exact mul_le_mul_of_nonneg_left hm1_pow (by positivity)
          _ = a * t ^ (2 * p) := by dsimp [t]; ring
          _ ≤ g t := hloc
      · have htm1_le : tau S * m₁ ≤ t := mul_le_mul_of_nonneg_left hmx.le htau_pos.le
        have htm1_nn : 0 ≤ tau S * m₁ := mul_nonneg htau_pos.le hm₁_pos.le
        have hmono_g : g (tau S * m₁) ≤ g t :=
          hg_mono (Set.mem_Ici.mpr htm1_nn) (Set.mem_Ici.mpr (mul_nonneg htau_pos.le hx0)) htm1_le
        have hloc := hg_local (tau S * m₁) htm1_nn hm₁_leδ
        have hpowx : x ^ (2 * p) ≤ 1 := pow_le_one₀ hx0 hx1
        calc
          c * x ^ (2 * p) ≤ c * 1 := mul_le_mul_of_nonneg_left hpowx hc_pos.le
          _ = a * (tau S * m₁) ^ (2 * p) := by dsimp [c]; ring
          _ ≤ g (tau S * m₁) := hloc
          _ ≤ g t := hmono_g
    linarith
  rcases le_total 0 m with hm0 | hm0
  · exact hnonneg_case m hm0 (abs_le.mp hm).2
  · have hnm0 : 0 ≤ -m := neg_nonneg.mpr hm0
    have hnm1 : -m ≤ 1 := by linarith [(abs_le.mp hm).1]
    have hres := hnonneg_case (-m) hnm0 hnm1
    rw [P3aG_rateI_even S m hm] at hres
    have heven2 : (-m) ^ 2 = m ^ 2 := by ring
    have heven2p : (-m) ^ (2 * p) = m ^ (2 * p) := by
      rw [pow_mul, pow_mul, neg_sq]
    rw [heven2, heven2p] at hres
    exact hres

end CritWinSpin

open CritWinSpin

theorem solution (S : SpinLaw) (hS : IsGHS S) (p : ℕ) (hp : IsTypeP S p) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, |m| ≤ 1 →
        (tau S / 2) * m ^ 2 + c * m ^ (2 * p) ≤ rateI S m :=
  P3aG_global_lower S hS p hp
