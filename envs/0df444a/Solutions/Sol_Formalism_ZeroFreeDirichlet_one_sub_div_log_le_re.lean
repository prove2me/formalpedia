-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.one_sub_div_log_le_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:06.678795+00:00
-- url     : https://prove2.me/submissions/f6cd7074-cf43-4c92-869e-e4357bbaa37a

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZFRDirichletOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_one_le_natCast
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_mul_abs_add_two_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {c cz : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (hcz : 0 < cz) (h : c ≤ cz)
    (hs : InRegion c q s) : 1 - cz / Real.log (|s.im| + 2) ≤ s.re := by
  unfold InRegion at hs
  have hq := one_le_natCast q
  have hT : (2 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hlogT : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith)
  have hle : Real.log (|s.im| + 2) ≤ Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hLpos := log_mul_abs_add_two_pos q s.im
  have h1 := div_le_div_of_nonneg_right h hLpos.le
  have h2 := div_le_div_of_nonneg_left hcz.le hlogT hle
  linarith
end Formalism.ZeroFreeDirichlet
