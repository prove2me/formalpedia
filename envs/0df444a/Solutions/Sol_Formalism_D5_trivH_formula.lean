-- Prove2me | solution 1 for Formalism.D5.trivH_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:57.754804+00:00
-- url     : https://prove2.me/submissions/cf55a040-5f45-4c77-b6da-6c5ca25a2f78

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Theorems.Thm_Formalism_D5_zmod_two_cases_bis
import Theorems.Thm_Formalism_D5_zmod_two_one_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5
theorem _root_.solution (ψ : AddChar (E0 × H) ℂ) (hψ : TrivH ψ) (g : E0 × H) :
    ψ g = (if g.1.1 = 0 then 1 else ψ e10) * (if g.1.2 = 0 then 1 else ψ e01) := by
  obtain ⟨⟨a, b⟩, h⟩ := g
  have h0 : ψ ((0, 0), h) = 1 := hψ h
  rcases zmod_two_cases_bis a with rfl | rfl <;> rcases zmod_two_cases_bis b with rfl | rfl
  · simp [h0]
  · have e : ((((0 : ZMod 2), (1 : ZMod 2)), h) : E0 × H) = e01 + ((0, 0), h) := by simp [e01]
    conv_lhs => rw [e]
    rw [AddChar.map_add_eq_mul, h0]
    simp [zmod_two_one_ne_zero]
  · have e : ((((1 : ZMod 2), (0 : ZMod 2)), h) : E0 × H) = e10 + ((0, 0), h) := by simp [e10]
    conv_lhs => rw [e]
    rw [AddChar.map_add_eq_mul, h0]
    simp [zmod_two_one_ne_zero]
  · have e : ((((1 : ZMod 2), (1 : ZMod 2)), h) : E0 × H) = e10 + e01 + ((0, 0), h) := by
      simp [e10, e01]
    conv_lhs => rw [e]
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h0]
    simp [zmod_two_one_ne_zero]
end Formalism.D5
