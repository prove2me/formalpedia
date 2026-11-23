-- Prove2me | solution 1 for Formalism.QuantumDeterminants.linear_operators_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:20.858333+00:00
-- url     : https://prove2.me/submissions/638d675d-32c7-4951-b414-17915add405f

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
import Theorems.Thm_Formalism_QuantumDeterminants_WRPres_differentiableAt_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open WRPres
namespace Formalism.QuantumDeterminants
theorem _root_.solution : LinOps := by
  intro m E _ _ l i f g a hf hg
  have hd : ∀ x ∈ OmX m, DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ g x :=
    fun x hx => ⟨differentiableAt_of_mem hf hx, differentiableAt_of_mem hg hx⟩
  fin_cases i <;> refine ⟨funext fun x => ?_, funext fun x => ?_⟩ <;>
    simp only [opL, pOp, cOp, ciOp, pbOp, cbOp, cbiOp, wirt, wirtBar, Pi.add_apply, Pi.smul_apply,
      Fin.isValue] <;>
    (try split_ifs with hx) <;>
    (try (have e1 : fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x :=
            fderiv_add (hd x hx).1 (hd x hx).2
          rw [e1])) <;>
    (try (have e2 : fderiv ℝ (a • f) x = a • fderiv ℝ f x := by
            first
            | exact fderiv_const_smul (hd x hx).1 a
            | exact fderiv_const_smul a (hd x hx).1
          rw [e2])) <;>
    (try simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_zero, add_zero]) <;>
    module
end Formalism.QuantumDeterminants
