-- Prove2me | solution 1 for Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:56:15.301404+00:00
-- url     : https://prove2.me/submissions/aa338146-90b8-4fe8-ba88-6d75084dc260

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_finiteDimensional_Q0_alt
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_Kur_eq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kur_eq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Kur_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_Kn


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
theorem _root_.solution {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : ∃ a : ℚ_[l], ‖x‖ = ‖a‖ := by
  rw [← Kur_eq] at hx
  obtain ⟨n, hn, hxn⟩ := (LocalClassField.mem_Kur_iff finiteDimensional_Q0_alt x).1 hx
  obtain ⟨y, hy, h⟩ := LocalClassField.norm_Kn l (Q0 l) finiteDimensional_Q0_alt hn hxn
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hy
  exact ⟨a, h.trans (PadicAlgCl.norm_extends l a)⟩
end Formalism.MainNotions.N.PreambleDegrees.Loc
