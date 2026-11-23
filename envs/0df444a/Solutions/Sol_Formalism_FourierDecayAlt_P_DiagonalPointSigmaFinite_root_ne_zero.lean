-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.root_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:22.971913+00:00
-- url     : https://prove2.me/submissions/d9c10990-6e1f-42e3-b161-07c14e70e936

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
theorem _root_.solution {m : ℕ} {Kc : Set ℂ} (h0 : (0 : ℂ) ∉ Kc) {D : ℂ} (hD : D ∈ Kc) {z : ℂ}
    (hz : z ^ (m + 2) = (-1) ^ (m + 3) * D) : z ≠ 0 := by
  rintro rfl
  rw [zero_pow (by omega)] at hz
  have h1 : D = 0 := by
    rcases mul_eq_zero.mp hz.symm with h | h
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact h
  exact h0 (h1 ▸ hD)
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
