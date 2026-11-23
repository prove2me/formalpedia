-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.vdesc_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:52.61087+00:00
-- url     : https://prove2.me/submissions/6e49f909-e1b0-4588-bda6-ab9c244b9f91

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul

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
theorem _root_.solution (x a : ℕ) (ha : a ≤ x) :
    padicValNat p a.factorial ≤ padicValNat p (x.descFactorial a) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    padicValNat.mul (by positivity) (Nat.choose_pos ha).ne']
  omega
end Formalism.GM.gammaIntegralityLemmas
