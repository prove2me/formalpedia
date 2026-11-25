-- Prove2me | solution 1 for Formalism.MainNotions.N.PreambleDegrees.Loc.norm_one_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:48.079239+00:00
-- url     : https://prove2.me/submissions/f5425e9a-f6f5-4531-9fff-186e7ef0dc33

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_norm_l
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_prod_one_sub_primitiveRoots
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_norm_one_sub_eq

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
theorem _root_.solution {k : ℕ} (hk : 0 < k) {z : Om l} (hz : IsPrimitiveRoot z (l ^ k)) :
    ‖1 - z‖ ^ (l ^ k).totient = (l : ℝ)⁻¹ := by
  have hpos : 0 < l ^ k := pow_pos (Fact.out : l.Prime).pos k
  have h := congrArg norm (prod_one_sub_primitiveRoots (l := l) hk)
  rw [norm_prod, norm_l] at h
  rw [Finset.prod_congr rfl (fun x hx => norm_one_sub_eq ((mem_primitiveRoots hpos).mp hx) hz),
    Finset.prod_const, hz.card_primitiveRoots] at h
  exact h
end Formalism.MainNotions.N.PreambleDegrees.Loc
