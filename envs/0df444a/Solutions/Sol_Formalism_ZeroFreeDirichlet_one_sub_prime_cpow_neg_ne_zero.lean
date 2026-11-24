-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.one_sub_prime_cpow_neg_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:07.476235+00:00
-- url     : https://prove2.me/submissions/456b6fff-7da4-4557-ab8c-ec0b12267760

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TrivReal

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
theorem _root_.solution (p : ℕ) (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.1 h).symm
  have h2 := congrArg norm h1
  rw [norm_natCast_cpow_of_pos hp.pos, norm_one, neg_re] at h2
  have h3 : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  linarith
end Formalism.ZeroFreeDirichlet
