-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.regularized_bracket_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:26:02.240804+00:00
-- url     : https://prove2.me/submissions/65db8d41-97ec-4d62-ae5f-420ab98ced0b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_dil_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_support_positive

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
theorem _root_.solution (H : Hyp D Ξ α) {X Y X₁ Y₁ X₂ Y₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ q, D.inSS q → Ph D X Y q = Ph D X₁ Y₁ q + Ph D X₂ Y₂ q) {p : SS k r} (hp : D.inSS p) :
    regBracket D X Y p = fun x y => regBracket D X₁ Y₁ p x y + regBracket D X₂ Y₂ p x y := by
  funext x y
  unfold regBracket
  by_cases h1 : D.χ x = 0
  · simp [h1]
  by_cases h2 : D.χ y = 0
  · simp [h2]
  rw [h _ (dil_inSS H.dilN D hp (cutoff_support_positive D h1) (cutoff_support_positive D h2))]
  ring
end Formalism.FourierDecayAlt.P.B6
