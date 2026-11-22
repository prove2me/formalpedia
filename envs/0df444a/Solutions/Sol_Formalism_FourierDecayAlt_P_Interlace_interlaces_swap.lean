-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Interlace.interlaces_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:34.014971+00:00
-- url     : https://prove2.me/submissions/50260df9-7a41-4752-a202-700764e553ff

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
    Interlaces k u' u ρ := by
  intro i hi
  obtain ⟨a, b, c, d⟩ := h i hi
  exact ⟨b, a, d, c⟩
end Formalism.FourierDecayAlt.P.Interlace
