-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_coefOut_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:55:25.966206+00:00
-- url     : https://prove2.me/submissions/fd2f4b08-ddf8-423f-907e-0014cd13961b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lord_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_lord_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_valS_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_valS
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_eOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_eOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_eq_self_of_eOut_eq_zero
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_substS_monomial__39ec68064bef
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_substS
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_substS_eIn_eq_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_substS_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]
variable (sg : L → Bool) (S : Finset L)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hout : ∀ i ∈ S, ¬ out i) (μ : L × Fin r →₀ ℕ)
    (F : MvPolynomial (L × Fin r) K) : valS sg S F ≤ valS sg S (coefOut out μ F) := by
  rw [le_valS_iff]
  intro β
  by_cases hμ : ∃ α ∈ F.support, eOut out α = μ
  · obtain ⟨α₀, -, hα₀⟩ := hμ
    have hμ1 : eOut out μ = μ := by rw [← hα₀, eOut_eOut]
    have hμ2 : eIn out μ = 0 := by rw [← hα₀, eIn_eOut]
    have hexp : (subV sg S (coefOut out μ F)).coeff β =
        ∑ α ∈ F.support, if eOut out α = μ then
          lauι K r (F.coeff α) * (subV sg S (monomial (eIn out α) 1)).coeff β else 0 := by
      unfold coefOut
      rw [map_sum, coeff_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      split_ifs
      · rw [substS_monomial', coeff_C_mul]
      · rw [map_zero, coeff_zero]
    by_cases hβ : eOut out β = 0
    · have hβ2 : eIn out β = β := eIn_eq_self_of_eOut_eq_zero out hβ
      have : (subV sg S (coefOut out μ F)).coeff β = (subV sg S F).coeff (μ + β) := by
        rw [hexp, coeff_substS]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [coeff_substS_monomial _ sg S _ _ out hout α (μ + β), eOut_add, eIn_add, hμ1, hμ2, hβ, hβ2,
          add_zero, zero_add]
        by_cases h : eOut out α = μ
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero]
      rw [this]
      exact pge_valS sg S F _
    · rw [hexp]
      refine le_lord_sum _ _ fun α _ => ?_
      split_ifs
      · rw [coeff_substS_eIn_eq_zero _ sg S _ _ out α β hβ, mul_zero, lord_zero]; exact le_top
      · rw [lord_zero]; exact le_top
  · have : coefOut out μ F = 0 := by
      unfold coefOut
      refine Finset.sum_eq_zero fun α hα => ?_
      rw [if_neg fun h => hμ ⟨α, hα, h⟩]
    rw [this, map_zero, coeff_zero, lord_zero]; exact le_top
end Formalism.MainNotions.PlaneGram
