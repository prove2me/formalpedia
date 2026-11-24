-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.exceptional_zero_bound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:59:07.098954+00:00
-- url     : https://prove2.me/submissions/4394bec3-b1f3-4f25-bf51-caf7be987e36

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExcBoundOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_le_const_mul_rpow
import Theorems.Thm_Formalism_ZeroFreeDirichlet_rpow_neg_eq_inv_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : ExcBoundOf := by
  unfold ExcBoundOf ExcBound
  intro hS hL ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨c0, hc0, hS'⟩ := hS (ε / 3) hε3
  obtain ⟨C, hC⟩ := hL
  obtain ⟨K, hK, hKb⟩ := log_le_const_mul_rpow (ε / 3) hε3
  obtain ⟨M, hM, hCM⟩ : ∃ M : ℝ, 0 < M ∧ C ≤ M := ⟨max C 1, lt_max_of_lt_right one_pos, le_max_left _ _⟩
  have hcpos : 0 < min (1 / K) (c0 / (M * K ^ 2)) :=
    lt_min (div_pos one_pos hK) (div_pos hc0 (mul_pos hM (pow_pos hK 2)))
  refine ⟨min (1 / K) (c0 / (M * K ^ 2)), hcpos, ?_⟩
  intro q _ χ β hχ2 hχ1 hβ
  have hcK : min (1 / K) (c0 / (M * K ^ 2)) ≤ 1 / K := min_le_left _ _
  have hc2 : min (1 / K) (c0 / (M * K ^ 2)) ≤ c0 / (M * K ^ 2) := min_le_right _ _
  generalize min (1 / K) (c0 / (M * K ^ 2)) = c at hcpos hcK hc2 ⊢
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hu1 : 1 ≤ (q : ℝ) ^ (ε / 3) := Real.one_le_rpow hq1 hε3.le
  have hqε : (q : ℝ) ^ (-ε) = (((q : ℝ) ^ (ε / 3)) ^ 3)⁻¹ := by
    have h := rpow_neg_eq_inv_pow (q : ℝ) ε hq0 3 (by norm_num)
    simpa using h
  have hq3 : (q : ℝ) ^ (-(ε / 3)) = ((q : ℝ) ^ (ε / 3))⁻¹ := Real.rpow_neg hq0.le _
  have hlogK : Real.log (3 * q) ≤ K * (q : ℝ) ^ (ε / 3) := hKb q hq1
  have hlog_pos : 0 < Real.log (3 * q) := Real.log_pos (by linarith)
  have hβ1 : β < 1 := by
    by_contra hge
    simp only [not_lt] at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simpa using hge) hβ
  have hlow := hS' q χ hχ2 hχ1
  rw [hq3] at hlow
  rw [hqε]
  generalize (q : ℝ) ^ (ε / 3) = u at hu1 hlogK hlow ⊢
  have hu0 : 0 < u := by linarith
  by_cases hcase : β ≤ 1 - 1 / Real.log (3 * q)
  · have key : c * Real.log (3 * q) ≤ u ^ 3 := by
      have hu3 : u ≤ u ^ 3 := le_self_pow₀ hu1 (by norm_num)
      calc c * Real.log (3 * q) ≤ (1 / K) * (K * u) :=
            mul_le_mul hcK hlogK hlog_pos.le (div_pos one_pos hK).le
        _ = u := by field_simp
        _ ≤ u ^ 3 := hu3
    have h1 : c * (u ^ 3)⁻¹ ≤ 1 / Real.log (3 * q) := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hu0 3) hlog_pos, one_mul]
      exact key
    linarith
  · simp only [not_le] at hcase
    have hdiff := DirichletCharacter.differentiable_LFunction hχ1
    have hmvt : ‖(fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) 1 -
        (fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) β‖ ≤
        (C * Real.log (3 * q) ^ 2) * (1 - β) := by
      refine norm_image_sub_le_of_norm_deriv_le_segment'
        (f := fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) (a := β) (b := 1)
        (f' := fun t : ℝ => deriv (DirichletCharacter.LFunction χ) (t : ℂ)) ?_ ?_ 1 ⟨hβ1.le, le_refl _⟩
      · intro t _
        exact ((hdiff (t : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
      · intro t ht
        exact hC q χ hχ1 t (by linarith [ht.1]) ht.2.le
    simp only [hβ, sub_zero, Complex.ofReal_one] at hmvt
    have h1β : 0 < 1 - β := by linarith
    have hlog2 : Real.log (3 * q) ^ 2 ≤ (K * u) ^ 2 := pow_le_pow_left₀ hlog_pos.le hlogK 2
    have hCle : C * Real.log (3 * q) ^ 2 ≤ M * (K * u) ^ 2 :=
      mul_le_mul hCM hlog2 (sq_nonneg _) hM.le
    have hmain : c0 * u⁻¹ ≤ M * (K * u) ^ 2 * (1 - β) :=
      le_trans hlow (le_trans hmvt (mul_le_mul_of_nonneg_right hCle h1β.le))
    have hc0' : c0 ≤ M * K ^ 2 * u ^ 3 * (1 - β) := by
      have h := mul_le_mul_of_nonneg_right hmain hu0.le
      have e1 : c0 * u⁻¹ * u = c0 := by field_simp
      have e2 : M * (K * u) ^ 2 * (1 - β) * u = M * K ^ 2 * u ^ 3 * (1 - β) := by ring
      linarith
    have hMKu : 0 < M * K ^ 2 * u ^ 3 := mul_pos (mul_pos hM (pow_pos hK 2)) (pow_pos hu0 3)
    have hfin : c * (u ^ 3)⁻¹ ≤ 1 - β := by
      calc c * (u ^ 3)⁻¹ ≤ c0 / (M * K ^ 2) * (u ^ 3)⁻¹ :=
            mul_le_mul_of_nonneg_right hc2 (inv_nonneg.2 (pow_pos hu0 3).le)
        _ = c0 / (M * K ^ 2 * u ^ 3) := by field_simp
        _ ≤ 1 - β := by
          rw [div_le_iff₀ hMKu]
          linarith
    linarith
end Formalism.ZeroFreeDirichlet
