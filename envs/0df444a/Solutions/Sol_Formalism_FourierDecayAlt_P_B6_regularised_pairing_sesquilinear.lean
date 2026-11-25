-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.regularised_pairing_sesquilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:43:59.155257+00:00
-- url     : https://prove2.me/submissions/2d7cba05-3f8b-4834-8f89-b37861b31c11

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_weighted_of_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_of_weighted
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_phase_function_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_phase_function_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_pairing_smul_left_bis
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_phase_function_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_betaInfTau_additive_of_pairing_additive
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regularised_pairing_smul

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
theorem _root_.solution (H : Hyp D Ξ α) {τ : ℝ × ℝ} (hτ : τ ∈ Quad) : SesqOn (InCC α 4) (betaInfTau D τ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x x' y ⟨c, hc⟩ ⟨c', hc'⟩ ⟨d, hd⟩
    have hx := admissible_weighted_of_bound hc
    have hx' := admissible_weighted_of_bound hc'
    have hy := admissible_weighted_of_bound hd
    exact betaInfTau_additive_of_pairing_additive H hx hy hx' hy
      (fun q hq => phase_function_add_left H (admissible_of_weighted hx) (admissible_of_weighted hx') (admissible_of_weighted hy) hq) hτ
  · rintro x y y' ⟨c, hc⟩ ⟨d, hd⟩ ⟨d', hd'⟩
    have hx := admissible_weighted_of_bound hc
    have hy := admissible_weighted_of_bound hd
    have hy' := admissible_weighted_of_bound hd'
    exact betaInfTau_additive_of_pairing_additive H hx hy hx hy'
      (fun q hq => phase_function_add_right H (admissible_of_weighted hx) (admissible_of_weighted hy) (admissible_of_weighted hy') hq) hτ
  · intro a x y _ _
    exact regularised_pairing_smul D a (fun q => pairing_smul_left_bis D a x y q) τ
  · intro a x y _ _
    exact regularised_pairing_smul D (conj a) (fun q => phase_function_smul_right D a x y q) τ
end Formalism.FourierDecayAlt.P.B6
