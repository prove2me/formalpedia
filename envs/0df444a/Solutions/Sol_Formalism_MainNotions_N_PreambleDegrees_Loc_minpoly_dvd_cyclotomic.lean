-- Prove2me | solution 1 for Formalism.MainNotions.N.PreambleDegrees.Loc.minpoly_dvd_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:29.640054+00:00
-- url     : https://prove2.me/submissions/5eaa5994-474d-4819-825c-ed4e25426e94

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
variable {F : IntermediateField ℚ_[l] (Om l)}
namespace Formalism.MainNotions.N.PreambleDegrees.Loc
theorem _root_.solution {k : ℕ} {z : Om l} (hz : IsPrimitiveRoot z (l ^ k)) :
    minpoly F z ∣ cyclotomic (l ^ k) F := by
  apply minpoly.dvd
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
  exact (hz.isRoot_cyclotomic (pow_pos (Fact.out : l.Prime).pos k)).eq_zero
end Formalism.MainNotions.N.PreambleDegrees.Loc
