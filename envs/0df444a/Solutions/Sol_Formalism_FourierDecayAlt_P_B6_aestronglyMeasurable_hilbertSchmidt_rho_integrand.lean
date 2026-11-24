-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.aestronglyMeasurable_hilbertSchmidt_rho_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:28:45.674225+00:00
-- url     : https://prove2.me/submissions/76ebb1a2-fb1a-4265-8156-fa5ebc2fbb1c

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_two_sided_translate
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_ae_strongly_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inSS_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_sgs_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hsInner_continuous
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv


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
    AEStronglyMeasurable (fun g : Mt k r => hsInner (rho D p A (Matrix.of g)) (B (Matrix.of g))) D.μG := by
  have hxy := inSS_mem D hp
  have hAt : AEStronglyMeasurable (fun g : Mt k r => A (sgs p (Matrix.of g))) D.μG := by
    simp only [sgs_eq]
    exact admissible_ae_strongly_measurable (admissible_two_sided_translate H.α_nonneg hA (WeylGroupFacts.uh_inv hxy.1) hxy.2) D.haarG
  have h1 : AEStronglyMeasurable (fun g : Mt k r => Sd D p (A (sgs p (Matrix.of g)))) D.μG :=
    (Sd D p).continuous.comp_aestronglyMeasurable hAt
  exact hsInner_continuous.comp_aestronglyMeasurable (h1.prodMk (admissible_ae_strongly_measurable hB D.haarG))
end Formalism.FourierDecayAlt.P.B6
