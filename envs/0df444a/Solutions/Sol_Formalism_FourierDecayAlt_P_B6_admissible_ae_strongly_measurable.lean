-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.admissible_ae_strongly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:34:59.850865+00:00
-- url     : https://prove2.me/submissions/e33e3e22-e3fb-46a1-bd28-94c6536da1be

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_isClosed_GV
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_ae

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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α c : ℝ} {f : Mat k r → E}
    (hf : admitted α c f) {μ : Measure (Mt k r)} (h : IsHaarOn (GV k r) μ) :
    AEStronglyMeasurable (fun g : Mt k r => f (Matrix.of g)) μ := by
  have hcl : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ GV k r} := isClosed_GV k r
  have hm : MeasurableSet {x : Mt k r | (Matrix.of x : Mat k r) ∈ GV k r} := hcl.measurableSet
  have hc : ContinuousOn (fun g : Mt k r => f (Matrix.of g)) {x : Mt k r | (Matrix.of x : Mat k r) ∈ GV k r} :=
    hf.1
  have h1 := hc.aestronglyMeasurable (μ := μ) hm
  have h2 : μ.restrict {x : Mt k r | (Matrix.of x : Mat k r) ∈ GV k r} = μ :=
    Measure.restrict_eq_self_of_ae_mem (haar_ae h)
  rwa [h2] at h1
end Formalism.FourierDecayAlt.P.B6
