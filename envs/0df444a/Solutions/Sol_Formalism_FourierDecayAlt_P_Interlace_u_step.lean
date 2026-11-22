-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Interlace.u_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:54:28.890092+00:00
-- url     : https://prove2.me/submissions/3b0fc39b-afc1-4677-9275-5291a93e1eaf

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Interlace
open Finset Formalism.FourierDecayAlt.I
namespace Formalism.FourierDecayAlt.P.Interlace
theorem _root_.solution {k : ℕ} {u u' ρ : ℕ → ℝ} (h : Interlaces k u u' ρ) :
    ∀ i, 1 ≤ i → i + 1 ≤ k → u (i + 1) ≤ u i := by
  intro i h1 h2
  obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨h1, by omega⟩)
  linarith
end Formalism.FourierDecayAlt.P.Interlace
