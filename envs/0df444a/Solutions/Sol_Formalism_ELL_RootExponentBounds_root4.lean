-- Prove2me | solution 1 for Formalism.ELL.RootExponentBounds.root4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:11.046265+00:00
-- url     : https://prove2.me/submissions/6a898990-b0e3-4efc-ac63-5b49fa23e846

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
theorem _root_.solution {c a b d e r : K} (hc : ‖c‖ = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (he : ‖e‖ ≤ 1) (h : c * r ^ 4 + a * r ^ 3 + b * r ^ 2 + d * r + e = 0) : ‖r‖ ≤ 1 := by
  by_contra hr; push Not at hr
  have e' : c * r ^ 4 = -(a * r ^ 3 + b * r ^ 2 + d * r ^ 1 + e * r ^ 0) := by
    linear_combination h
  have hb' : ‖a * r ^ 3 + b * r ^ 2 + d * r ^ 1 + e * r ^ 0‖ ≤ ‖r‖ ^ 3 :=
    addle (addle (addle (tb 3 3 ha hr.le le_rfl) (tb 2 3 hb hr.le (by norm_num)))
      (tb 1 3 hd hr.le (by norm_num))) (tb 0 3 he hr.le (by norm_num))
  rw [← norm_neg, ← e', norm_mul, norm_pow, hc, one_mul] at hb'
  have : ‖r‖ ^ 3 < ‖r‖ ^ 4 := pow_lt_pow_right₀ hr (by norm_num)
  linarith
end Formalism.ELL.RootExponentBounds
