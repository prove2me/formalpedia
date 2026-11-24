-- Prove2me | solution 1 for Formalism.CohomologicalDescent.jw_gate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:57:39.191633+00:00
-- url     : https://prove2.me/submissions/60d4a966-9f70-4144-92a0-4ea8f27df0c2

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_StatementC
import Definitions.Def_Formalism_PieriBlockIdeals_JointCW5
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound

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
open Formalism Formalism.CohomologicalDescent
open Formalism.RankGapBounds.ChebyshevFactorialBounds
namespace Formalism.CohomologicalDescent
theorem _root_.solution {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) :
    (0 : ℝ) ≤ (if ((D.d0 τ l : ℕ) : ℤ) < Cor.DB D τ then
        min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ)) else 0) := by
  split_ifs
  · exact le_min (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact le_rfl
end Formalism.CohomologicalDescent
