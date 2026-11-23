-- Prove2me | solution 1 for Formalism.ELL.deuring_model
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:08.629087+00:00
-- url     : https://prove2.me/submissions/b1bf8c1c-536e-48d6-a2c9-ba3c407782c9

import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LegendreInvariant
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Deuring
import Theorems.Thm_Formalism_ELL_DeuringModel_norm_add_eq_left
import Theorems.Thm_Formalism_ELL_DeuringModel_norm_nat_le_one
import Theorems.Thm_Formalism_ELL_DeuringModel_exists_root_deuring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ELL
open DeuringModel
namespace Formalism.ELL
theorem _root_.solution : ModelDeuring := by
  intro K _ _ _ h3 j hj
  obtain ⟨a, ha⟩ := exists_root_deuring j
  have hc4 : (deuring a).c₄ = a * (a ^ 3 - 24) := by
    simp [deuring, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hΔ : (deuring a).Δ = a ^ 3 - 27 := by
    simp [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have h27 : ‖(27 : K)‖ = 1 := by
    have e : (27 : K) = 3 ^ 3 := by norm_num
    rw [e, norm_pow, h3, one_pow]
  have ha1 : ‖a‖ ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have hA3 : ‖a ^ 3‖ = ‖a‖ ^ 3 := norm_pow a 3
    have hbig : 1 < ‖a‖ ^ 3 := one_lt_pow₀ hlt (by norm_num)
    have h24 : ‖(24 : K)‖ ≤ 1 := by exact_mod_cast norm_nat_le_one (K := K) 24
    have hn1 : ‖a ^ 3 - 24‖ = ‖a‖ ^ 3 := by
      rw [sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]
    have hn2 : ‖a ^ 3 - 27‖ = ‖a‖ ^ 3 := by
      rw [sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]
    have hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = ‖a‖ ^ 12 := by
      rw [norm_mul, hA3, norm_pow, hn1]
      ring
    have hR : ‖j * (a ^ 3 - 27)‖ ≤ ‖a‖ ^ 3 := by
      rw [norm_mul, hn2]
      calc ‖j‖ * ‖a‖ ^ 3 ≤ 1 * ‖a‖ ^ 3 := by gcongr
        _ = ‖a‖ ^ 3 := one_mul _
    rw [ha] at hL
    have hlt2 : ‖a‖ ^ 3 < ‖a‖ ^ 12 := pow_lt_pow_right₀ hlt (by norm_num)
    linarith
  have hA3le : ‖a ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha1
  have hΔle : ‖a ^ 3 - 27‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA3le (by rw [norm_neg, h27]))
  have hΔ1 : ‖a ^ 3 - 27‖ = 1 := by
    by_contra hne
    have hlt : ‖a ^ 3 - 27‖ < 1 := lt_of_le_of_ne hΔle hne
    have e1 : a ^ 3 = 27 + (a ^ 3 - 27) := by ring
    have hA : ‖a ^ 3‖ = 1 := by
      rw [e1, norm_add_eq_left (by rw [h27]; exact hlt), h27]
    have e2 : a ^ 3 - 24 = 3 + (a ^ 3 - 27) := by ring
    have hB : ‖a ^ 3 - 24‖ = 1 := by
      rw [e2, norm_add_eq_left (by rw [h3]; exact hlt), h3]
    have hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = 1 := by
      rw [norm_mul, hA, norm_pow, hB]
      norm_num
    rw [ha, norm_mul] at hL
    have h4 : ‖j‖ * ‖a ^ 3 - 27‖ < 1 := by
      calc ‖j‖ * ‖a ^ 3 - 27‖ ≤ 1 * ‖a ^ 3 - 27‖ := by gcongr
        _ < 1 := by rw [one_mul]; exact hlt
    linarith
  refine ⟨a, ha1, ?_, ?_⟩
  · rw [hc4, hΔ, ← ha]
    ring
  · rw [hΔ, hΔ1]
end Formalism.ELL
