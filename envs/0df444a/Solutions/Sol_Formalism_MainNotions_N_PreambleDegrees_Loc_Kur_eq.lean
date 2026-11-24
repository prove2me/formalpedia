-- Prove2me | solution 1 for Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:27.988816+00:00
-- url     : https://prove2.me/submissions/ffc88ec7-b9a4-4db7-8e16-b3893c9ee160

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_finiteDimensional_Q0_alt
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kur_eq


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
theorem _root_.solution : LocalClassField.MaximalUnramifiedExtension l (Q0 l) = MaximalUnramifiedExtension l := by
  rw [LocalClassField.Kur_eq finiteDimensional_Q0_alt, bot_sup_eq, MaximalUnramifiedExtension]
  congr 1
  ext x
  constructor
  · rintro ⟨m, hm, hx⟩
    exact ⟨m, Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l)), hm, hx⟩
  · rintro ⟨m, -, hm, hx⟩
    exact ⟨m, hm, hx⟩
end Formalism.MainNotions.N.PreambleDegrees.Loc
