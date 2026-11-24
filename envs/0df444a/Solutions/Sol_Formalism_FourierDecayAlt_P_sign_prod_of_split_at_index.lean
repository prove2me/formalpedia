-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.sign_prod_of_split_at_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:11.386802+00:00
-- url     : https://prove2.me/submissions/a9ff98a7-7361-4f02-867d-4d01233ccb1c

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (s : Finset ℕ) (g : ℕ → ℝ) (m : ℕ) (hpos : ∀ j ∈ s, j < m → 0 < g j)
    (hneg : ∀ j ∈ s, m ≤ j → g j < 0) : 0 < (-1 : ℝ) ^ (s.filter (m ≤ ·)).card * ∏ j ∈ s, g j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ih' := ih (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
      (fun j hj => hneg j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert ha, Finset.filter_insert]
    by_cases hma : m ≤ a
    · rw [if_pos hma, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.1 h).1), pow_succ]
      have := hneg a (Finset.mem_insert_self a s) hma
      nlinarith
    · rw [if_neg hma]
      have := hpos a (Finset.mem_insert_self a s) (by omega)
      nlinarith
end Formalism.FourierDecayAlt.P
