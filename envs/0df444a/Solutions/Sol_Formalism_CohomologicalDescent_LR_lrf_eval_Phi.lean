-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_eval_Phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:08.213304+00:00
-- url     : https://prove2.me/submissions/1283d8bc-de3d-4772-9712-eb6a10f82c3a

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_pt_L
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
theorem _root_.solution (F : MvPolynomial (Fin r × Fin n) R) :
    eval (lrf_idS R r n) (lrfc_Phi (lrf_L r n) (lrfc_iota F)) = eval₂ C (lrf_ell R r n) F := by
  have h : ((eval (lrf_idS R r n)).comp ((lrfc_Phi (R := R) (lrf_L r n)).toRingHom.comp lrfc_iota)) =
      eval₂Hom C (lrf_ell R r n) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, lrfc_iota,
        map_C, coe_eval₂Hom, eval₂_C]
      have hC : lrfc_Phi (lrf_L r n) (C (C c)) = C (C c : MvPolynomial (Fin r × Fin n) R) :=
        (lrfc_Phi (lrf_L r n)).commutes (C c)
      rw [hC, eval_C]
    · intro v
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, lrfc_iota,
        map_X, coe_eval₂Hom, eval₂_X]
      exact lrf_pt_L v
  exact congrArg (fun φ => φ F) h
end Formalism.CohomologicalDescent.LR
