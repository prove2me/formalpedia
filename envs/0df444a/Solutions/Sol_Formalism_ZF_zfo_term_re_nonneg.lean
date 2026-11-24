-- Prove2me | solution 1 for Formalism.ZF.zfo_term_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:43:09.588336+00:00
-- url     : https://prove2.me/submissions/fd4bcd05-73b5-494e-b37f-f67c7ede7419

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoTermReNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {z ρ : ℂ} (n : ℕ) (h : ρ.re < z.re) :
    0 ≤ ((n : ℂ) / (z - ρ)).re := by
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero, Complex.sub_re]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) (by linarith)) (Complex.normSq_nonneg _)
end Formalism.ZF
