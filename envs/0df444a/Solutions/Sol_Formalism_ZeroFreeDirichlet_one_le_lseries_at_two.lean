-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.one_le_lseries_at_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:05.949994+00:00
-- url     : https://prove2.me/submissions/a46d794b-20ba-4dac-9315-21bc0ebfd534

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
theorem _root_.solution {a : ℕ → ℂ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) : 1 ≤ LSeries a 2 := by
  have hlt : LSeries.abscissaOfAbsConv a < ((2 : ℂ).re : EReal) := by
    have e : ((2 : ℂ).re : EReal) = ((2 : ℝ) : EReal) := by norm_num
    rw [e]
    exact lt_of_le_of_lt habs (by exact_mod_cast (by norm_num : (1 : ℝ) < 2))
  have hs : LSeriesSummable a 2 := LSeriesSummable_of_abscissaOfAbsConv_lt_re hlt
  have h1 : LSeries.term a 2 1 = 1 := by simp [LSeries.term, ha1]
  have hnn : ∀ j, 0 ≤ LSeries.term a 2 j := fun j => by simpa using LSeries.term_nonneg (ha0 j) 2
  rw [← h1]
  exact hs.le_tsum 1 (fun j _ => hnn j)
end Formalism.ZeroFreeDirichlet
