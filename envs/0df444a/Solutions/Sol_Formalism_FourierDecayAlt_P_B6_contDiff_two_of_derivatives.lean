-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.contDiff_two_of_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:06:10.640399+00:00
-- url     : https://prove2.me/submissions/2f22fd2b-0742-4308-ba3b-f3d9707d0690

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {f f1 f2 : ℝ → ℂ} (h0 : ∀ t, HasDerivAt f (f1 t) t) (h1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hc : Continuous f2) : ContDiff ℝ 2 f := by
  have e1 : deriv f = f1 := funext fun t => (h0 t).deriv
  have e2 : deriv f1 = f2 := funext fun t => (h1 t).deriv
  have c1 : ContDiff ℝ 1 f1 := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun t => (h1 t).differentiableAt, by rw [e2]; exact hc⟩
  have : ContDiff ℝ (1 + 1) f := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun t => (h0 t).differentiableAt, by simp, by rw [e1]; exact c1⟩
  simpa [one_add_one_eq_two] using this
end Formalism.FourierDecayAlt.P.B6
