-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_choose_lucas
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:59.867625+00:00
-- url     : https://prove2.me/submissions/79226181-3077-47fd-9545-1272d0330665

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPowerSeries Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {l : ℕ} (hl : l.Prime) (c : ℕ) :
    ∀ a : ℕ, (l ^ a * c).choose (l ^ a) ≡ c [MOD l] := by
  haveI := Fact.mk hl
  intro a
  induction a with
  | zero => simp [Nat.ModEq]
  | succ a ih =>
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := l * (l ^ a * c))
      (k := l * l ^ a) (p := l)
    rw [Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hl.pos,
      Nat.mul_div_cancel_left _ hl.pos, Nat.choose_self, one_mul] at h
    rw [pow_succ', mul_assoc]
    exact h.trans ih
end Formalism.DworkPowerSeriesWeights
