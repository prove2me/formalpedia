-- Prove2me | solution 1 for Formalism.G.LogCR.Agree.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:12.200035+00:00
-- url     : https://prove2.me/submissions/ba3dbdc0-f5bb-40b4-9bce-5e992876d92b

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogCR
variable {R : Type*} [CommRing R] {σ τ : Type*}
namespace Formalism.G.LogCR
namespace Agree
theorem _root_.solution {N M : ℕ} {f g : MvPowerSeries σ R} (h : Agree N f g) (hMN : M ≤ N) :
    Agree M f g := fun d hd => h d (lt_of_lt_of_le hd hMN)
end Agree
end Formalism.G.LogCR
