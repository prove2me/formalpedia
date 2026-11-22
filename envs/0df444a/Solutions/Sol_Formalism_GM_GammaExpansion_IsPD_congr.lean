-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.IsPD.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:02.800486+00:00
-- url     : https://prove2.me/submissions/46097407-6fdc-4e04-bde1-515a740e76d2

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open Polynomial Finset
variable {k : Type} [Field k] [CharZero k]
namespace Formalism.GM.GammaExpansion
namespace IsPD
theorem _root_.solution {N0 d : ℕ} {g g' : ℕ → k} (h : IsPD N0 d g) (hg : ∀ n, N0 ≤ n → g' n = g n) :
    IsPD N0 d g' := by
  obtain ⟨P, hP, hP'⟩ := h
  exact ⟨P, hP, fun n hn => (hg n hn).trans (hP' n hn)⟩
end IsPD
end Formalism.GM.GammaExpansion
