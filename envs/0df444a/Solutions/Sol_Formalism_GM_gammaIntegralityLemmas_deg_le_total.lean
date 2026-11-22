-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.deg_le_total
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:57.248208+00:00
-- url     : https://prove2.me/submissions/136a9ed4-722d-45bf-a763-b952023e1c15

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (LL : Letters (N + 1)) (i : Fin (N + 1)) : LL.deg i ≤ LL.total :=
  Finset.single_le_sum (f := LL.deg) (fun _ _ => Nat.zero_le _) (mem_univ i)
end Formalism.GM.gammaIntegralityLemmas
