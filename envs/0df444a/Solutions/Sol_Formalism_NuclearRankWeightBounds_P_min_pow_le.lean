-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.min_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:11:21.150795+00:00
-- url     : https://prove2.me/submissions/478e5cb2-65e7-440f-aeb0-6cfaef4c863d

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LatSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution (t : ℝ) (ht : 0 < t) (K : ℕ) (hK : 3 ≤ K) :
    min 1 (t ^ K) ≤ t ^ ((K : ℝ) - 5 / 2) * ((min 1 t) ^ (5 / 4 : ℝ) * (min 1 t) ^ (5 / 4 : ℝ)) := by
  have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  rcases le_or_gt t 1 with h | h
  · rw [min_eq_right h, min_eq_right (pow_le_one₀ ht.le h)]
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_natCast]
    apply le_of_eq
    congr 1
    ring
  · rw [min_eq_left h.le, Real.one_rpow, mul_one, mul_one]
    refine (min_le_left _ _).trans ?_
    exact Real.one_le_rpow h.le (by linarith)
end Formalism.NuclearRankWeightBounds.P
