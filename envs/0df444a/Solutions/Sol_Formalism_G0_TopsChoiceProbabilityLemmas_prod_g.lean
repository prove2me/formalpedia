-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.prod_g
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:20.205282+00:00
-- url     : https://prove2.me/submissions/67a01ddd-f143-472b-8933-67bd4b6c1a7e

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsChoiceProbabilityLemmas
theorem _root_.solution (X Y : ℝ) (m : ℕ) :
    ∏ c ∈ Icc 1 (2 * m + 1), (if Odd c then X else Y) = X ^ (m + 1) * Y ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by ring, prod_Icc_succ_top (by omega),
      show 2 * m + 2 = (2 * m + 1) + 1 by ring, prod_Icc_succ_top (by omega), ih]
    have h1 : ¬ Odd (2 * m + 1 + 1) := by
      rw [Nat.not_odd_iff_even]
      exact ⟨m + 1, by ring⟩
    have h2 : Odd (2 * m + 1 + 1 + 1) := ⟨m + 1, by ring⟩
    rw [if_neg h1, if_pos h2]
    ring
end Formalism.G0.TopsChoiceProbabilityLemmas
