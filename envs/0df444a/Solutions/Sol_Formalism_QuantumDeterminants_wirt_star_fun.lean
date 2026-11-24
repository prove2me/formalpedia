-- Prove2me | solution 1 for Formalism.QuantumDeterminants.wirt_star_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:12:38.042524+00:00
-- url     : https://prove2.me/submissions/acb8818d-b4ae-41a4-b03e-54e9b44593b5

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
theorem _root_.solution (l : Fin m) (g : (Fin m → ℂ) → ℂ) (x : Fin m → ℂ) :
    wirt l (fun y => star (g y)) x = star (wirtBar l g x) := by
  unfold wirt wirtBar
  rw [fderiv_star]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul, Complex.star_def, map_add, map_mul, map_div₀, map_one, map_ofNat,
    Complex.conj_I]
  ring
end Formalism.QuantumDeterminants
