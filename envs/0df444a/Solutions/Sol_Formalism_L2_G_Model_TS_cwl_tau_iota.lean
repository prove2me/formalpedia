-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cwl_tau_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:59:34.035421+00:00
-- url     : https://prove2.me/submissions/d1e4e98c-36a8-4584-a8cb-938597083c56

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
theorem _root_.solution (l : Fin r × Fin r × (Fin r × Fin n)) (F : MvPolynomial (Fin r × Fin n) R) :
    cwl_tau l (cwl_iota F) =
      Polynomial.eval₂ cwl_iota (C (X l.2.2)) (rowGen R l.1 l.2.1 F) := by
  have h : ((cwl_tau (R := R) l).toRingHom.comp cwl_iota) =
      (Polynomial.eval₂RingHom cwl_iota (C (X l.2.2))).comp (rowGen R l.1 l.2.1).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [cwl_tau, cwl_iota, rowGen]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      simp only [cwl_tau, cwl_iota, rowGen, aeval_X, map_X, Polynomial.coe_eval₂RingHom]
      split_ifs
      · simp
        exact mul_comm _ _
      · simp
  exact congrArg (fun φ => φ F) h
end Formalism.L2.G.Model.TS
