-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.norm_fact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:24.651883+00:00
-- url     : https://prove2.me/submissions/78cade93-809c-4a60-a94b-2d3502545c8c

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_nat_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (t : ℕ) : ‖(t.factorial : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p t.factorial : ℤ)) :=
  norm_nat_eq _ (Nat.factorial_pos t).ne'
end Formalism.GM.gammaIntegralityLemmas
