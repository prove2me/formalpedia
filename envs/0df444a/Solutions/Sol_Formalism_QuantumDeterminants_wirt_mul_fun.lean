-- Prove2me | solution 1 for Formalism.QuantumDeterminants.wirt_mul_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:12:26.226394+00:00
-- url     : https://prove2.me/submissions/13b25adb-86ba-4839-b4bc-7efaf8a7f801

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
variable {m : ℕ}
namespace Formalism.QuantumDeterminants
theorem _root_.solution (l : Fin m) {a b : (Fin m → ℂ) → ℂ} {x : Fin m → ℂ}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    wirt l (fun y => a y * b y) x = wirt l a x * b x + a x * wirt l b x := by
  unfold wirt
  rw [show (fun y => a y * b y) = a * b from rfl, fderiv_mul ha hb]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end Formalism.QuantumDeterminants
