-- Prove2me | solution 1 for Formalism.MainNotions.G.ValuationFitting.Em_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:40:00.628279+00:00
-- url     : https://prove2.me/submissions/5093c728-9e33-4b6f-8dba-e2c83ac75532

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ValuationFitting
open ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.G.ValuationFitting
theorem _root_.solution {m h : ℕ} (hmh : m ≤ h) : (Em R m h).submatrix id (Fin.castLE hmh) = 1 := by
  ext j k
  simp only [Em, Matrix.submatrix_apply, Matrix.of_apply, id_eq, Fin.coe_castLE, Matrix.one_apply]
  by_cases hjk : j = k
  · subst hjk
    simp
  · rw [if_neg (fun e => hjk (Fin.ext e.symm)), if_neg hjk]
end Formalism.MainNotions.G.ValuationFitting
