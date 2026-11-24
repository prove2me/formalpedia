-- Prove2me | solution 1 for Formalism.MainNotions.N.PreambleDegrees.Loc.norm_one_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:53.624099+00:00
-- url     : https://prove2.me/submissions/bd46b740-06e8-41e0-9001-b5ece26930e6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_norm_eq_one_of_pow
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_norm_one_sub_pow_le
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_eq_one_of_pow


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
theorem _root_.solution {k : ℕ} {z z' : Om l} (hz : IsPrimitiveRoot z (l ^ k))
    (hz' : IsPrimitiveRoot z' (l ^ k)) : ‖1 - z‖ = ‖1 - z'‖ := by
  have hpos : l ^ k ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have n1 : ‖z‖ ≤ 1 := (norm_eq_one_of_pow hpos hz.pow_eq_one).le
  have n2 : ‖z'‖ ≤ 1 := (norm_eq_one_of_pow hpos hz'.pow_eq_one).le
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one hz'.pow_eq_one
  obtain ⟨j, -, hj⟩ := hz'.eq_pow_of_pow_eq_one hz.pow_eq_one
  apply le_antisymm
  · rw [← hj]
    exact norm_one_sub_pow_le n2 j
  · rw [← hi]
    exact norm_one_sub_pow_le n1 i
end Formalism.MainNotions.N.PreambleDegrees.Loc
