-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.unit_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:53:43.428805+00:00
-- url     : https://prove2.me/submissions/96dbd351-9229-4f0c-91e1-77f3b268b52b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma norm_le_lemma_2 {A : Mat k r} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖A i j‖ ≤ c) :
    ‖A‖ ≤ c := by
  first
    | exact (Matrix.norm_le_iff hc).mpr h
    | exact (pi_norm_le_iff_of_nonneg hc).mpr fun i => (pi_norm_le_iff_of_nonneg hc).mpr (h i)
section
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
end
end Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {X : Mat k r} (h : unitLie k r X) : ‖X‖ ≤ 1 := by
  exact norm_le_lemma_2 zero_le_one h.2
end Formalism.FourierDecayAlt.P.B4
