-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cw_eval_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:58:10.781203+00:00
-- url     : https://prove2.me/submissions/31e5b25d-ab38-4115-99d5-b442210c6257

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
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
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (l : Fin r × Fin r × (Fin r × Fin n)) (y : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    eval y (cwl_tau l G) = eval (cwUpd l y) G := by
  have h : (eval y).comp (cwl_tau (R := R) l).toRingHom = eval (cwUpd l y) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [cwl_tau]
    · intro v
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        cwl_tau, aeval_X, cwUpd, eval_X, map_add]
      split_ifs <;> simp
  exact congrArg (fun φ => φ G) h
end Formalism.L2.G.Model.TS
