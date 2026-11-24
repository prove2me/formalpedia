-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.gam_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:26:28.986776+00:00
-- url     : https://prove2.me/submissions/c69e05c3-f434-447e-a130-b3e4c4763197

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_zero_outside
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_derivative_zero_outside
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_iteratedDeriv_two_eq_zero_off_support

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
theorem _root_.solution {W : ℝ → ℝ} (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2) (ρ : ℝ) (m : ℕ) {t : ℝ}
    (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2) : gam ρ W m t = 0 := by
  match m with
  | 0 => simp [gam, cutoff_zero_outside hWs ht, iteratedDeriv_two_eq_zero_off_support hWs ht]
  | 1 => simp [gam, cutoff_zero_outside hWs ht, cutoff_derivative_zero_outside hWs ht]
  | (n + 2) => simp [gam, cutoff_zero_outside hWs ht]
end Formalism.FourierDecayAlt.P.B6
