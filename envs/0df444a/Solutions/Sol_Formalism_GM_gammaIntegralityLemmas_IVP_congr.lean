-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IVP.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:47.401403+00:00
-- url     : https://prove2.me/submissions/b3135f18-d647-4b50-aab4-32da6fe15673

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
namespace IVP
theorem _root_.solution {D : ℕ} {g h : ℕ → ℚ_[p]} (hg : IVP p D g) (e : ∀ m, g m = h m) : IVP p D h := by
  have : g = h := funext e
  rw [← this]; exact hg
end IVP
end Formalism.GM.gammaIntegralityLemmas
