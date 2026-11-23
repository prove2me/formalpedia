-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.ld_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:22:49.096669+00:00
-- url     : https://prove2.me/submissions/24c62639-bc85-462c-a953-a6a3f395c13a

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (q : ℕ) (s x : ℝ) (hx : 0 < x) : ld q (fun y => y ^ s) x = s ^ q * x ^ s := by
  unfold ld
  have : (fun u : ℝ => (Real.exp u) ^ s) = fun u : ℝ => Real.exp (s * u) := by
    funext u; rw [mul_comm, Real.exp_mul]
  rw [this, iteratedDeriv_exp_const_mul]
  show s ^ q * Real.exp (s * Real.log x) = _
  rw [mul_comm s, Real.exp_mul, Real.exp_log hx]
end Formalism.FourierDecayAlt.P.LEx1
