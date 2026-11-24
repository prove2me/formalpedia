-- Prove2me | solution 1 for Formalism.L2.DIV.we_eval_idFrame_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:56:16.08954+00:00
-- url     : https://prove2.me/submissions/a5908c39-56d4-4cea-b1a8-0431470e66d1

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.DIV
theorem _root_.solution {r n : ℕ} (G : MvPolynomial (Fin r × Fin n) ℤ) :
    eval (idFrame ℚ r n) (MvPolynomial.map (Int.castRingHom ℚ) G) = ((eval (idFrame ℤ r n) G : ℤ) : ℚ) := by
  have h : idFrame ℚ r n = fun v => (Int.castRingHom ℚ) (idFrame ℤ r n v) := by
    funext v
    unfold idFrame
    split_ifs <;> simp
  rw [h, eval_map, ← eval₂_id]
  exact (eval₂_comp_left (Int.castRingHom ℚ) (RingHom.id ℤ) (idFrame ℤ r n) G).symm
end Formalism.L2.DIV
