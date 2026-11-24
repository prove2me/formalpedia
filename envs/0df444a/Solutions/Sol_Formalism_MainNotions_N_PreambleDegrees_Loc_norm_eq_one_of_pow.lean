-- Prove2me | solution 1 for Formalism.MainNotions.N.PreambleDegrees.Loc.norm_eq_one_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:31.537626+00:00
-- url     : https://prove2.me/submissions/4eb18bcb-2f49-4b14-99e6-d5528e8d37cc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots

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
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) {z : Om l} (hz : z ^ n = 1) : ‖z‖ = 1 := by
  have h := congrArg norm hz
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h
end Formalism.MainNotions.N.PreambleDegrees.Loc
