-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.cutoff_mul_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:06:02.229348+00:00
-- url     : https://prove2.me/submissions/e66e7afc-7ce0-4115-a01f-c630140fc741

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
theorem _root_.solution {v : ℝ → ℝ} (hv : Continuous v) (h0 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v t = 0) {q : ℝ → ℂ}
    (hq : ContinuousOn q (Set.Ioi 0)) : Continuous (fun t => (v t : ℂ) * q t) := by
  have e : (fun t => (v t : ℂ) * q t) = fun t => (v t : ℂ) * q (max t (1 / 2)) := by
    funext t
    by_cases ht : (1 / 2 : ℝ) ≤ t
    · rw [max_eq_left ht]
    · rw [h0 t (fun h => ht h.1.le)]; simp
  rw [e]
  refine (Complex.continuous_ofReal.comp hv).mul
    (hq.comp_continuous (continuous_id.max continuous_const) fun t => ?_)
  show (0 : ℝ) < max t (1 / 2)
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _)
end Formalism.FourierDecayAlt.P.B6
