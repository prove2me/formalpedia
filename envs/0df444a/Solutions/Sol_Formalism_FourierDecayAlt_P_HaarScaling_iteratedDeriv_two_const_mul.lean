-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HaarScaling.iteratedDeriv_two_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:09.430313+00:00
-- url     : https://prove2.me/submissions/310daeb6-9a11-4d76-910d-4ccbd250cd9f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarScaling
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.HaarScaling
theorem _root_.solution (c : ℂ) (f : ℝ → ℂ) :
    iteratedDeriv 2 (fun x => c * f x) = fun x => c * iteratedDeriv 2 f x := by
  have h2 : ∀ g : ℝ → ℂ, iteratedDeriv 2 g = deriv (deriv g) := by
    intro g
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, h2, deriv_const_mul_field', deriv_const_mul_field']
end Formalism.FourierDecayAlt.P.HaarScaling
