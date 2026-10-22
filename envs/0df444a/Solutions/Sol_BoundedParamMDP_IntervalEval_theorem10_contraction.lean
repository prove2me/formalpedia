-- Prove2me | solution 1 for BoundedParamMDP.IntervalEval.theorem10_contraction
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:58:52.088472+00:00
-- url     : https://prove2.me/submissions/0692d94a-1329-4766-ae47-d1d5c6aa3627

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP
import Definitions.Def_BoundedParamMDP_IntervalEval_IntervalPolicyEvaluation
set_option autoImplicit false
open BoundedParamMDP.Optimal BoundedParamMDP.IntervalEval

theorem ll_sumF {Q : Type*} [Fintype Q] (F : Q → ℝ) (h0 : ∀ q, 0 ≤ F q) (h1 : ∑ q, F q = 1)
    (w : Q → ℝ) : |∑ q, F q * w q| ≤ ‖w‖ := by
  calc |∑ q, F q * w q| ≤ ∑ q, |F q * w q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, F q * ‖w‖ := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        rw [abs_mul, abs_of_nonneg (h0 q)]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm w q) (h0 q)
    _ = ‖w‖ := by rw [← Finset.sum_mul, h1, one_mul]

theorem ll_vipol_diff {Q A : Type*} [Fintype Q] (M : MDP Q A) (π : Policy Q A) (u v : Q → ℝ)
    (p : Q) : |VIpol M π v p - VIpol M π u p| ≤ M.γ * ‖v - u‖ := by
  have : VIpol M π v p - VIpol M π u p = M.γ * ∑ q, M.F p (π p) q * (v - u) q := by
    simp only [VIpol, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]; ring
  rw [this, abs_mul, abs_of_nonneg M.γ_nonneg]
  exact mul_le_mul_of_nonneg_left (ll_sumF _ (M.F_nonneg p (π p)) (M.F_sum p (π p)) _) M.γ_nonneg

theorem ll_vipol_bnd {Q A : Type*} [Fintype Q] (M : MDP Q A) (π : Policy Q A) (v : Q → ℝ)
    (p : Q) : |VIpol M π v p - M.R p| ≤ M.γ * ‖v‖ := by
  have : VIpol M π v p - M.R p = M.γ * ∑ q, M.F p (π p) q * v q := by
    simp only [VIpol]; ring
  rw [this, abs_mul, abs_of_nonneg M.γ_nonneg]
  exact mul_le_mul_of_nonneg_left (ll_sumF _ (M.F_nonneg p (π p)) (M.F_sum p (π p)) _) M.γ_nonneg

theorem ll_iInf_dist {ι : Type*} (a b : ι → ℝ) (ha : BddBelow (Set.range a))
    (hb : BddBelow (Set.range b)) (d : ℝ) (hd0 : 0 ≤ d) (h : ∀ i, |a i - b i| ≤ d) :
    |(⨅ i, a i) - ⨅ i, b i| ≤ d := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Real.iInf_of_isEmpty, sub_self, abs_zero]
    exact hd0
  · have h1 : (⨅ i, a i) - d ≤ ⨅ i, b i := by
      refine le_ciInf (fun i => ?_)
      have := (abs_le.mp (h i)).2
      have := ciInf_le ha i
      linarith
    have h2 : (⨅ i, b i) - d ≤ ⨅ i, a i := by
      refine le_ciInf (fun i => ?_)
      have := (abs_le.mp (h i)).1
      have := ciInf_le hb i
      linarith
    rw [abs_le]; constructor <;> linarith

theorem ll_iSup_dist {ι : Type*} (a b : ι → ℝ) (ha : BddAbove (Set.range a))
    (hb : BddAbove (Set.range b)) (d : ℝ) (hd0 : 0 ≤ d) (h : ∀ i, |a i - b i| ≤ d) :
    |(⨆ i, a i) - ⨆ i, b i| ≤ d := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Real.iSup_of_isEmpty, sub_self, abs_zero]
    exact hd0
  · have h1 : (⨆ i, a i) ≤ (⨆ i, b i) + d := by
      refine ciSup_le (fun i => ?_)
      have := (abs_le.mp (h i)).2
      have := le_ciSup hb i
      linarith
    have h2 : (⨆ i, b i) ≤ (⨆ i, a i) + d := by
      refine ciSup_le (fun i => ?_)
      have := (abs_le.mp (h i)).1
      have := le_ciSup ha i
      linarith
    rw [abs_le]; constructor <;> linarith

theorem solution {Q A : Type*} [Fintype Q] [Fintype A] [Nonempty A]
    (B : BoundedParamMDP.Optimal.BMDP Q A) (π : BoundedParamMDP.Optimal.Policy Q A) :
    IsContraction (IVIlo B π) ∧ IsContraction (IVIhi B π) := by
  have hb : ∀ (v : Q → ℝ) (p : Q) (M : Member B), |VIpol M.1 π v p - B.R p| ≤ B.γ * ‖v‖ := by
    intro v p M
    have := ll_vipol_bnd M.1 π v p
    rwa [M.2.1, M.2.2.1] at this
  have hd : ∀ (u v : Q → ℝ) (p : Q) (M : Member B),
      |VIpol M.1 π v p - VIpol M.1 π u p| ≤ B.γ * ‖v - u‖ := by
    intro u v p M
    have := ll_vipol_diff M.1 π u v p
    rwa [M.2.2.1] at this
  have hg : 0 ≤ B.γ := B.γ_nonneg
  refine ⟨⟨B.γ, hg, B.γ_lt_one, fun u v => ?_⟩, ⟨B.γ, hg, B.γ_lt_one, fun u v => ?_⟩⟩
  · rw [pi_norm_le_iff_of_nonneg (mul_nonneg hg (norm_nonneg _))]
    intro p
    rw [Real.norm_eq_abs, Pi.sub_apply]
    refine ll_iInf_dist _ _ ?_ ?_ _ (mul_nonneg hg (norm_nonneg _)) (fun M => hd u v p M)
    · refine ⟨B.R p - B.γ * ‖v‖, ?_⟩
      rintro _ ⟨M, rfl⟩
      have := (abs_le.mp (hb v p M)).1; linarith
    · refine ⟨B.R p - B.γ * ‖u‖, ?_⟩
      rintro _ ⟨M, rfl⟩
      have := (abs_le.mp (hb u p M)).1; linarith
  · rw [pi_norm_le_iff_of_nonneg (mul_nonneg hg (norm_nonneg _))]
    intro p
    rw [Real.norm_eq_abs, Pi.sub_apply]
    refine ll_iSup_dist _ _ ?_ ?_ _ (mul_nonneg hg (norm_nonneg _)) (fun M => hd u v p M)
    · refine ⟨B.R p + B.γ * ‖v‖, ?_⟩
      rintro _ ⟨M, rfl⟩
      have := (abs_le.mp (hb v p M)).2; linarith
    · refine ⟨B.R p + B.γ * ‖u‖, ?_⟩
      rintro _ ⟨M, rfl⟩
      have := (abs_le.mp (hb u p M)).2; linarith
