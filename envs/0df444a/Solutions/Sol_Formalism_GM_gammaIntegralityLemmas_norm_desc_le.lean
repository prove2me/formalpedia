-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.norm_desc_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:32.133082+00:00
-- url     : https://prove2.me/submissions/47e62f30-a62a-4fe0-8f1d-3019a99a7081

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_norm_natCast_le_one__a9d2d1dd10a2
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_zpow_pos__da61b7487fff
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_fact

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
theorem _root_.solution (x a : ℕ) : ‖((x.descFactorial a : ℕ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(padicValNat p a.factorial : ℤ)) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, norm_mul, norm_fact]
  have h1 := norm_natCast_le_one' (p := p) (x.choose a)
  have h2 := zpow_pos' (p := p) (-(padicValNat p a.factorial : ℤ))
  nlinarith [norm_nonneg ((x.choose a : ℕ) : ℚ_[p])]
end Formalism.GM.gammaIntegralityLemmas
