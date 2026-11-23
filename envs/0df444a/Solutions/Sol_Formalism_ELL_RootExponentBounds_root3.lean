-- Prove2me | solution 1 for Formalism.ELL.RootExponentBounds.root3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:13.39308+00:00
-- url     : https://prove2.me/submissions/0860e745-5c55-4fc8-ba53-ffb4af232624

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_ChangeIntegral
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Change
import Theorems.Thm_Formalism_ELL_RootExponentBounds_addle
import Theorems.Thm_Formalism_ELL_RootExponentBounds_tb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ELL Formalism.G
open Formalism Formalism.ELL Formalism.ELL.RootExponentBounds
universe u
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.RootExponentBounds
theorem _root_.solution {c a b d r : K} (hc : ‖c‖ = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (h : c * r ^ 3 + a * r ^ 2 + b * r + d = 0) : ‖r‖ ≤ 1 := by
  by_contra hr; push Not at hr
  have e : c * r ^ 3 = -(a * r ^ 2 + b * r ^ 1 + d * r ^ 0) := by linear_combination h
  have hb' : ‖a * r ^ 2 + b * r ^ 1 + d * r ^ 0‖ ≤ ‖r‖ ^ 2 :=
    addle (addle (tb 2 2 ha hr.le le_rfl) (tb 1 2 hb hr.le (by norm_num)))
      (tb 0 2 hd hr.le (by norm_num))
  rw [← norm_neg, ← e, norm_mul, norm_pow, hc, one_mul] at hb'
  have : ‖r‖ ^ 2 < ‖r‖ ^ 3 := pow_lt_pow_right₀ hr (by norm_num)
  linarith
end Formalism.ELL.RootExponentBounds
