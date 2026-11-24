-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.cutoff_product_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:06:03.887027+00:00
-- url     : https://prove2.me/submissions/6e3a020c-d6dd-43e0-979d-5d66285b07e9

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
theorem _root_.solution {u u' : ℝ → ℝ} (hu : ∀ t, HasDerivAt u (u' t) t) (hu0 : ∀ t, t ≤ 0 → u =ᶠ[𝓝 t] 0)
    {q q' : ℝ → ℂ} (hq : ∀ t, 0 < t → HasDerivAt q (q' t) t) (t : ℝ) :
    HasDerivAt (fun t => (u t : ℂ) * q t) ((u' t : ℂ) * q t + (u t : ℂ) * q' t) t := by
  by_cases ht : 0 < t
  · exact (hu t).ofReal_comp.mul (hq t ht)
  · have h0 := hu0 t (not_lt.1 ht)
    have e0 : u t = 0 := h0.eq_of_nhds
    have e1 : u' t = 0 := by
      have := (hu t).deriv
      rw [h0.deriv_eq] at this
      simpa using this.symm
    rw [e0, e1]
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    refine (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [h0] with s hs
    simp [hs]
end Formalism.FourierDecayAlt.P.B6
