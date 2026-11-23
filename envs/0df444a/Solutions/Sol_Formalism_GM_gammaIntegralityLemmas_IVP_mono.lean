-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IVP.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:26.599999+00:00
-- url     : https://prove2.me/submissions/3bcf4780-e61a-4afc-ae0e-2621c64814aa

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
theorem _root_.solution {D D' : ℕ} {g : ℕ → ℚ_[p]} (h : IVP p D g) (hD : D ≤ D') : IVP p D' g := by
  obtain ⟨⟨P, hP, hPg⟩, hn⟩ := h
  exact ⟨⟨P, hP.trans hD, hPg⟩, hn⟩
end IVP
end Formalism.GM.gammaIntegralityLemmas
