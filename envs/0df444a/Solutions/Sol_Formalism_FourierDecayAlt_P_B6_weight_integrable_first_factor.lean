-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.weight_integrable_first_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:08:39.08409+00:00
-- url     : https://prove2.me/submissions/e7c907d8-fd3e-4489-ac43-d6d6a65f1d5f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_lam_continuous

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {Ξ : Mat k r → NNReal} (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r × Mt k r))
    (hm : Measurable fun x : Mt k r => Ξ (Matrix.of x))
    (h : (∫⁻ p : Mt k r × Mt k r, Ξ (Matrix.of p.2 * Matrix.of p.1) *
      ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ))) ∂μ) < ∞) :
    Integrable (fun p : Mt k r × Mt k r => (Ξ (Matrix.of p.2 * Matrix.of p.1) : ℝ) *
      (1 + |lam k r z (Matrix.of p.2)|) ^ (-2 : ℝ)) μ := by
  let mm : Mt k r × Mt k r → Mt k r := fun p => (Matrix.of p.2 * Matrix.of p.1 : Mat k r)
  have cm : Continuous mm := Continuous.matrix_mul continuous_snd continuous_fst
  have m1 : Measurable (fun p : Mt k r × Mt k r => Ξ (Matrix.of p.2 * Matrix.of p.1)) :=
    hm.comp (cm.measurable)
  have c2 : Continuous (fun p : Mt k r × Mt k r => lam k r z (Matrix.of p.2)) :=
    (lam_continuous k r z).comp continuous_snd
  have m2 : Measurable (fun p : Mt k r × Mt k r => (1 + |lam k r z (Matrix.of p.2)|) ^ (-2 : ℝ)) := by
    have : Measurable (fun p : Mt k r × Mt k r => lam k r z (Matrix.of p.2)) := c2.measurable
    fun_prop
  refine ⟨(m1.coe_nnreal_real.mul m2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) h
  refine lintegral_congr fun p => ?_
  rw [enorm_mul, Real.enorm_eq_ofReal (NNReal.coe_nonneg _), Real.enorm_eq_ofReal (by positivity),
    ENNReal.ofReal_coe_nnreal]
end Formalism.FourierDecayAlt.P.B6
