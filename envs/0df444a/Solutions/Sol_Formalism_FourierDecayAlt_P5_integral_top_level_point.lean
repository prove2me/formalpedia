-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.integral_top_level_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:45:24.190733+00:00
-- url     : https://prove2.me/submissions/9f1a39f4-c782-4edc-a981-c27b7020477c

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution {β E : Type} [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Measure β) [SFinite ν]
    (f : Cf r (Fin.last r) × β → E) :
    (Integrable f (volume.prod ν) ↔ Integrable (fun g => f (lastLevelPoint r, g)) ν) ∧
      ∫ q, f q ∂(volume.prod ν) = ∫ g, f (lastLevelPoint r, g) ∂ν := by
  have hv : (volume : Measure (Cf r (Fin.last r))) = Measure.dirac (lastLevelPoint r) := by
    rw [volume_pi]; exact Measure.pi_of_empty _ _
  rw [hv, Measure.dirac_prod]
  exact ⟨(measurableEmbedding_prodMk_left _).integrable_map_iff,
    (measurableEmbedding_prodMk_left _).integral_map _⟩
end Formalism.FourierDecayAlt.P5
