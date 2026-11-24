-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.iteratedDeriv_lseries_alternating_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:08.707254+00:00
-- url     : https://prove2.me/submissions/9ec35f38-33eb-4e38-85a0-beb22091b822

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivInvSubOneAtTwo
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivLseriesAlternatingNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexOrder Nat
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {a : ℕ → ℂ} (ha0 : ∀ n, 0 ≤ a n)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) (n : ℕ) :
    0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n (LSeries a) 2 := by
  have hlt : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) :=
    lt_of_le_of_lt habs (by exact_mod_cast (by norm_num : (1 : ℝ) < 2))
  have h := LSeries.iteratedDeriv_alternating (a := a) (fun m => ha0 m) (x := 2) hlt n
  simpa using h
end Formalism.ZeroFreeDirichlet
