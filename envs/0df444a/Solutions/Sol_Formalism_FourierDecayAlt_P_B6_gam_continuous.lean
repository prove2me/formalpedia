-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.gam_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:27:47.597063+00:00
-- url     : https://prove2.me/submissions/813f5eb3-3888-4387-9be4-40a627da3ae8

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_div_pow_continuous

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
theorem _root_.solution {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2) (ρ : ℝ) (m : ℕ) : Continuous (gam ρ W m) := by
  have c0 : Continuous W := hW.continuous
  have c1 : Continuous (deriv W) := hW.continuous_deriv (by simp)
  have c2 : Continuous (iteratedDeriv 2 W) := (contDiff_infty.1 hW 2).continuous_iteratedDeriv 2 le_rfl
  have d0 := cutoff_div_pow_continuous c0 (fun t ht => cutoff_zero_outside hWs ht) 2
  have d1 := cutoff_div_pow_continuous c1 (fun t ht => cutoff_derivative_zero_outside hWs ht) 1
  match m with
  | 0 => exact c0.sub c2
  | 1 =>
    have : gam ρ W 1 = fun t => 2 * ρ * (deriv W t / t ^ 1) - ρ * (W t / t ^ 2) := by
      funext t; simp only [gam, pow_one]; ring
    rw [this]
    exact (continuous_const.mul d1).sub (continuous_const.mul d0)
  | (n + 2) =>
    have : gam ρ W (n + 2) = fun t => -(ρ ^ 2 * (W t / t ^ 2)) := by
      funext t; simp only [gam]; ring
    rw [this]
    exact (continuous_const.mul d0).neg
end Formalism.FourierDecayAlt.P.B6
