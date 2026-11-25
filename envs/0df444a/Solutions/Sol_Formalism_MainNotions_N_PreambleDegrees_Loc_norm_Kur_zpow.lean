-- Prove2me | solution 1 for Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:34.859421+00:00
-- url     : https://prove2.me/submissions/a9f28838-a532-4c8f-b902-152ab0ae325e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_norm_Kur

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.PreambleDegrees Formalism.MainNotions.N.PreambleDegrees.Loc
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups Polynomial
variable {l : ℕ} [Fact l.Prime]
variable (l)
variable {l}
namespace Formalism.MainNotions.N.PreambleDegrees.Loc
theorem _root_.solution {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h0 : x ≠ 0) : ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k := by
  obtain ⟨a, ha⟩ := norm_Kur hx
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at ha
    exact h0 ha
  refine ⟨-a.valuation, ?_⟩
  rw [ha]
  first
  | exact Padic.norm_eq_zpow_neg_valuation ha0
  | exact Padic.norm_eq_pow_val ha0
end Formalism.MainNotions.N.PreambleDegrees.Loc
