-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.edgeFactorBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:18:16.82736+00:00
-- url     : https://prove2.me/submissions/238f5784-6337-4ff4-bae0-db5cf091ef5f

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : FirstBound := by
  intro c Y l h hl hlk hY
  obtain ⟨hY1, hY2⟩ := hY
  have hk4 : (4 : ℝ) ≤ c.k := by exact_mod_cast h.hk
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hD := h.hDel
  have hvl : c.v l ≤ c.v 1 := by
    simp only [Cfg.v]; push_cast; nlinarith
  have hpos : 0 < 4 * (c.k : ℝ) * c.Del := by positivity
  have ha := h.ha
  have hv1 := h.hv1
  have h1 : 0 < c.a - c.v 1 := by linarith
  have h2 : c.a - c.v 1 ≤ c.a + 1 / 2 - -Y := by linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [Cfg.U1]; apply one_div_pos.mpr; linarith
  · simp only [Cfg.U1]; exact one_div_le_one_div_of_le h1 h2
  · have ha0 : 0 < c.a := by
      have : 0 ≤ c.v 1 := by
        simp only [Cfg.v]; have := h.hv0; push_cast; nlinarith
      linarith
    rw [div_le_div_iff₀ h1 ha0]; linarith
end Formalism.FourierDecayAlt.P
