-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IVP.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:45.643107+00:00
-- url     : https://prove2.me/submissions/d9e75026-7ce7-4cf3-91f0-f51651240d3a

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
theorem _root_.solution (D : ℕ) : IVP p D (fun _ => 0) :=
  ⟨⟨0, by simp, fun m => by simp⟩, fun m => by simp⟩
end IVP
end Formalism.GM.gammaIntegralityLemmas
