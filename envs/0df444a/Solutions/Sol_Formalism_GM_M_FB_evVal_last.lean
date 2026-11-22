-- Prove2me | solution 1 for Formalism.GM.M.FB.evVal_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:32.438788+00:00
-- url     : https://prove2.me/submissions/c6f98d61-b9a7-4eb3-9bf8-0153b8ca74d2

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.M.FB
theorem _root_.solution (ρ c : Fin r) :
    evVal p (N := N) ρ (Fin.last N, c) = if c = ρ then 1 else 0 := by
  simp [evVal]
end Formalism.GM.M.FB
