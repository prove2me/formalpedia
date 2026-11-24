-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.cutoff_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:32.712842+00:00
-- url     : https://prove2.me/submissions/106a5ed1-6eab-44b9-9693-2b4edb624ec0

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_product_continuous

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
theorem _root_.solution {v1 v2 : ℝ → ℝ} (hv1 : Continuous v1) (hv2 : Continuous v2)
    (h1 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v1 t = 0) (h2 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v2 t = 0)
    {q : ℝ → ℝ → ℂ} (hq : ContinuousOn (fun t : ℝ × ℝ => q t.1 t.2) Quad) {E : ℝ × ℝ → ℂ} (hE : Continuous E) :
    Integrable (fun t : ℝ × ℝ => ((v1 t.1 * v2 t.2 : ℝ) : ℂ) * q t.1 t.2 * E t) := by
  refine ((cutoff_product_continuous hv1 hv2 h1 h2 hq).mul hE).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro
    ((isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)).prod (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2))) fun t ht => ?_
  show ((v1 t.1 * v2 t.2 : ℝ) : ℂ) * q t.1 t.2 * E t = 0
  by_cases a1 : t.1 ∈ Set.Ioo (1 / 2 : ℝ) 2
  · by_cases a2 : t.2 ∈ Set.Ioo (1 / 2 : ℝ) 2
    · exact absurd ⟨⟨a1.1.le, a1.2.le⟩, ⟨a2.1.le, a2.2.le⟩⟩ ht
    · rw [h2 t.2 a2]; simp
  · rw [h1 t.1 a1]; simp
end Formalism.FourierDecayAlt.P.B6
