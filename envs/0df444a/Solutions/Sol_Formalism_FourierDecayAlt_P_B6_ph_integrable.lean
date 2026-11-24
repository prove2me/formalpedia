-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.ph_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:49:40.552795+00:00
-- url     : https://prove2.me/submissions/2e48362e-84a4-46bc-85b0-eaaad8b1a349

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inSS_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_translated_product_integrable_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aestronglyMeasurable_hilbertSchmidt_rho_integrand
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hilbert_schmidt_integrand_bound

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
theorem _root_.solution (H : Hyp D Ξ α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hB : admitted α cB B) {p : SS k r} (hp : D.inSS p) :
    Integrable (fun g : Mt k r => hsInner (rho D p A (Matrix.of g)) (B (Matrix.of g))) D.μG := by
  obtain ⟨K, -, hK⟩ := translated_product_integrable_bound H
  have hxy := inSS_mem D hp
  have h := (hK A B cA cB hA hB _ hxy.1 _ hxy.2).1
  exact (h.const_mul (Module.finrank ℂ Wq : ℝ)).mono' (aestronglyMeasurable_hilbertSchmidt_rho_integrand H hA hB hp)
    (Eventually.of_forall fun g => hilbert_schmidt_integrand_bound D A B hp _)
end Formalism.FourierDecayAlt.P.B6
