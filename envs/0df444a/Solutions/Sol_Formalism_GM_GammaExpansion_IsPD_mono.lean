-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.IsPD.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:45.633592+00:00
-- url     : https://prove2.me/submissions/444b6722-da79-4a56-9d4c-3d5c771d21d7

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
theorem _root_.solution {N0 d d' : ℕ} {g : ℕ → k} (h : IsPD N0 d g) (hd : d ≤ d') : IsPD N0 d' g := by
  obtain ⟨P, hP, hP'⟩ := h
  exact ⟨P, hP.trans hd, hP'⟩
end IsPD
end Formalism.GM.GammaExpansion
