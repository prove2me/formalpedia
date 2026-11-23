-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.root_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:22.965137+00:00
-- url     : https://prove2.me/submissions/e8e77c40-ac93-4c35-85e2-7a40136efd97

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution {m : ℕ} {Kc : Set ℂ} (hK : IsCompact Kc) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ D ∈ Kc, ∀ z : ℂ, z ^ (m + 2) = (-1) ^ (m + 3) * D → ‖z‖ ≤ R := by
  obtain ⟨R0, hR0⟩ := hK.isBounded.exists_norm_le
  refine ⟨max 1 R0, le_max_left _ _, fun D hD z hz => ?_⟩
  by_cases h1 : ‖z‖ ≤ 1
  · exact h1.trans (le_max_left _ _)
  · have h2 : ‖z‖ ≤ ‖z‖ ^ (m + 2) := le_self_pow₀ (not_le.mp h1).le (by omega)
    have h3 : ‖z‖ ^ (m + 2) = ‖D‖ := by
      rw [← norm_pow, hz, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact (h2.trans (h3.le.trans (hR0 D hD))).trans (le_max_right _ _)
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
