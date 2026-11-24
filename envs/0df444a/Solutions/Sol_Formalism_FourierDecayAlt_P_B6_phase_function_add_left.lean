-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.phase_function_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:05:51.107835+00:00
-- url     : https://prove2.me/submissions/9c65fb0f-a13d-43f0-b53c-4d8423020e57

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hsInner_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_rho_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ph_integrable

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
theorem _root_.solution (H : Hyp D Ξ α) {A₁ A₂ B : Mat k r → (Wq →L[ℂ] Wp)} {c₁ c₂ cB : ℝ} (h₁ : admitted α c₁ A₁)
    (h₂ : admitted α c₂ A₂) (hB : admitted α cB B) {q : SS k r} (hq : D.inSS q) :
    Ph D (A₁ + A₂) B q = Ph D A₁ B q + Ph D A₂ B q := by
  unfold Ph
  rw [← integral_add (ph_integrable H h₁ hB hq) (ph_integrable H h₂ hB hq)]
  congr 1
  funext g
  rw [rho_eq, rho_eq, rho_eq, Pi.add_apply, map_add, hsInner_add_left]
end Formalism.FourierDecayAlt.P.B6
