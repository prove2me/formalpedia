-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.LogEx.poinc_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:15.628481+00:00
-- url     : https://prove2.me/submissions/f3fb5a0c-4918-4165-bfdb-f2a85c6ee8d6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PoincEx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.LogEx
namespace Formalism.L2.FormalSeriesBounds.LogEx
theorem _root_.solution {σ K : Type} [CommRing K] (c : (σ →₀ ℕ) → K) :
    ∃ g : MvPowerSeries σ K, ∀ μ, coeff μ g = c μ :=
  ⟨c, fun _ => rfl⟩
end Formalism.L2.FormalSeriesBounds.LogEx
