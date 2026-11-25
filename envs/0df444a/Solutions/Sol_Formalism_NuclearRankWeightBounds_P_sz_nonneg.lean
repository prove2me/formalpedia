-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.sz_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:24:01.361237+00:00
-- url     : https://prove2.me/submissions/109a187e-1700-4b72-8bdc-eacd4e25cd40

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_ZLiftAsm

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
theorem _root_.solution {f : ℕ} (x : Fin f → ℝ) (K : ℕ) (z : Fin f → ℂ) (a : ℝ) (hx : ∀ v, 0 < x v) :
    0 ≤ sz x K z a := by
  unfold sz
  refine sum_nonneg fun A _ => mul_nonneg (prod_nonneg fun v _ => ?_) (sq_nonneg _)
  have := hx v
  positivity
end Formalism.NuclearRankWeightBounds.P
