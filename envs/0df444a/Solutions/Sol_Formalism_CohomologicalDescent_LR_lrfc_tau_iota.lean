-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrfc_tau_iota
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:19.72937+00:00
-- url     : https://prove2.me/submissions/748886c6-b553-473a-8a46-aefc00873bdf

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (l : Fin r × Fin r × (Fin r × Fin n)) (F : MvPolynomial (Fin r × Fin n) R) :
    lrfc_tau l (lrfc_iota F) =
      Polynomial.eval₂ lrfc_iota (C (X l.2.2)) (rowGen R l.1 l.2.1 F) := by
  have h : ((lrfc_tau (R := R) l).toRingHom.comp lrfc_iota) =
      (Polynomial.eval₂RingHom lrfc_iota (C (X l.2.2))).comp (rowGen R l.1 l.2.1).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lrfc_tau, lrfc_iota, rowGen]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      simp only [lrfc_tau, lrfc_iota, rowGen, aeval_X, map_X, Polynomial.coe_eval₂RingHom]
      split_ifs
      · simp
        exact mul_comm _ _
      · simp
  exact congrArg (fun φ => φ F) h
end Formalism.CohomologicalDescent.LR
