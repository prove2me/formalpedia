-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.derivBound_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:53.504885+00:00
-- url     : https://prove2.me/submissions/0438e878-649c-428f-9f76-ff80a360c3ec

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
theorem _root_.solution {s : ℕ} {k k' : ℕ} {Kd Kd' : Set ℂ} {bd : Mat s → ℝ} {Φ : Mat s → V}
    (h : DerivBound k Kd bd Φ) (hk : k' ≤ k) (hK : Kd' ⊆ Kd) : DerivBound k' Kd' bd Φ := by
  intro Z hZ
  obtain ⟨h1, h2⟩ := h Z (hK hZ)
  exact ⟨h1.of_le (by exact_mod_cast hk), fun j hj => h2 j (hj.trans hk)⟩
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
