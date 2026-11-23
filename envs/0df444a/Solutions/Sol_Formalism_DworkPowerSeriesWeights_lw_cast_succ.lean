-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.lw_cast_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:35.597284+00:00
-- url     : https://prove2.me/submissions/87d99193-9b9b-4279-a4f9-ab82fbaa0577

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity

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
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l d : ℕ) (s : ZMod d) : ((lw l s : ℤ) : ZMod (l + 1)) = 1 := by
  unfold lw
  have hl : ((l : ℤ) : ZMod (l + 1)) = -1 := by
    rw [Int.cast_natCast]
    have h : ((l + 1 : ℕ) : ZMod (l + 1)) = 0 := ZMod.natCast_self _
    rw [Nat.cast_add, Nat.cast_one] at h
    linear_combination h
  split_ifs with h
  · rw [Int.cast_mul, Int.cast_one, one_mul, Int.cast_pow, hl]
    exact Even.neg_one_pow (Nat.even_iff.mpr h)
  · rw [Int.cast_mul, Int.cast_neg, Int.cast_one, Int.cast_pow, hl,
      Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))]
    ring
end Formalism.DworkPowerSeriesWeights
