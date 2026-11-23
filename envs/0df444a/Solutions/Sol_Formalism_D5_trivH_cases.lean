-- Prove2me | solution 1 for Formalism.D5.trivH_cases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:44.638523+00:00
-- url     : https://prove2.me/submissions/1e1d3a1c-8217-46f6-ac1a-89518968454b

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Theorems.Thm_Formalism_D5_zmod_two_cases_bis
import Theorems.Thm_Formalism_D5_zmod_two_one_ne_zero
import Theorems.Thm_Formalism_D5_signZModTwo_zero
import Theorems.Thm_Formalism_D5_signZModTwo_one
import Theorems.Thm_Formalism_D5_trivH_formula
import Theorems.Thm_Formalism_D5_sq_one_of_order2
import Theorems.Thm_Formalism_D5_firstBasis_add_self
import Theorems.Thm_Formalism_D5_secondBasis_add_self

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
theorem _root_.solution (Hs : CycHost H) (ψ : AddChar (E0 × H) ℂ) (hψ : TrivH ψ) :
    ψ = 0 ∨ ψ = Hs.chC ∨ ψ = Hs.psC ∨ ψ = Hs.chpsC := by
  have hx := sq_one_of_order2 ψ e10 firstBasis_add_self
  have hy := sq_one_of_order2 ψ e01 secondBasis_add_self
  have key : ∀ g : E0 × H,
      ψ g = (if g.1.1 = 0 then 1 else ψ e10) * (if g.1.2 = 0 then 1 else ψ e01) :=
    trivH_formula ψ hψ
  rcases mul_self_eq_one_iff.mp hx with hx1 | hx1 <;>
    rcases mul_self_eq_one_iff.mp hy with hy1 | hy1
  · left
    ext ⟨⟨a, b⟩, h⟩
    rw [key, hx1, hy1, AddChar.zero_apply]
    simp
  · right; right; left
    ext ⟨⟨a, b⟩, h⟩
    rw [key, hx1, hy1, Hs.psC_apply]
    rcases zmod_two_cases_bis b with rfl | rfl <;> simp [signZModTwo_zero, signZModTwo_one, zmod_two_one_ne_zero]
  · right; left
    ext ⟨⟨a, b⟩, h⟩
    rw [key, hx1, hy1, Hs.chC_apply]
    rcases zmod_two_cases_bis a with rfl | rfl <;> simp [signZModTwo_zero, signZModTwo_one, zmod_two_one_ne_zero]
  · right; right; right
    ext ⟨⟨a, b⟩, h⟩
    rw [key, hx1, hy1, Hs.chpsC_apply]
    rcases zmod_two_cases_bis a with rfl | rfl <;> rcases zmod_two_cases_bis b with rfl | rfl <;>
      simp [signZModTwo_zero, signZModTwo_one, zmod_two_one_ne_zero]
end Formalism.D5
