-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.integrable_comp_bracket
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:33.809589+00:00
-- url     : https://prove2.me/submissions/dabc7026-0d70-457d-b2fa-969fe50f20b0

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν μ : Measure E) [ν.IsAddHaarMeasure] (k κ : NNReal)
    (hμ : μ = k • ν) (f : E → E) (hf : MeasurableEmbedding f) (hmap : Measure.map f μ = κ • μ) (A : ℝ)
    (hA : (Module.finrank ℝ E : ℝ) < A) : Integrable (fun p => (1 + ‖f p‖) ^ (-A)) μ := by
  have h0 : Integrable (fun q : E => (1 + ‖q‖) ^ (-A)) ν := integrable_one_add_norm hA
  have h1 : Integrable (fun q : E => (1 + ‖q‖) ^ (-A)) μ := hμ ▸ h0.smul_measure_nnreal
  have h2 : Integrable (fun q : E => (1 + ‖q‖) ^ (-A)) (Measure.map f μ) := hmap ▸ h1.smul_measure_nnreal
  exact hf.integrable_map_iff.1 h2
end Formalism.FourierDecayAlt.P.G7
