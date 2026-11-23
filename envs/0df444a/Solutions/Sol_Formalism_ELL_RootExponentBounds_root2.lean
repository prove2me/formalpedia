-- Prove2me | solution 1 for Formalism.ELL.RootExponentBounds.root2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:13.187869+00:00
-- url     : https://prove2.me/submissions/f0e6c693-b567-437f-ba89-6b17fc81b8f4

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
theorem _root_.solution {a b r : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (h : r ^ 2 + a * r + b = 0) :
    ‖r‖ ≤ 1 := by
  by_contra hr; push Not at hr
  have e : r ^ 2 = -(a * r ^ 1 + b * r ^ 0) := by linear_combination h
  have hb' : ‖a * r ^ 1 + b * r ^ 0‖ ≤ ‖r‖ ^ 1 :=
    addle (tb 1 1 ha hr.le le_rfl) (tb 0 1 hb hr.le (by norm_num))
  rw [← norm_neg, ← e, norm_pow] at hb'
  have : ‖r‖ ^ 1 < ‖r‖ ^ 2 := pow_lt_pow_right₀ hr (by norm_num)
  linarith
end Formalism.ELL.RootExponentBounds
