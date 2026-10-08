-- Prove2me | solution 1 for EkelandVP.General.bpLE_upper_closed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T15:06:47.624977+00:00
-- url     : https://prove2.me/submissions/cf6eea1e-8b0b-40d2-823d-b16512932878

import Mathlib
import Definitions.Def_EkelandVP_General_bpLE

set_option autoImplicit false

open EkelandVP.General in
theorem solution {V : Type*} [MetricSpace V] (α : ℝ) (p₁ : V × ℝ) :
    IsClosed {p : V × ℝ | bpLE α p₁ p} := by
  unfold bpLE
  exact isClosed_le (by fun_prop) continuous_const
