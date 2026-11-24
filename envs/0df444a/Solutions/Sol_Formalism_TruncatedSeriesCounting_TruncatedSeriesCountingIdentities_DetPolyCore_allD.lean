-- Prove2me | solution 1 for Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore.allD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:22:55.642301+00:00
-- url     : https://prove2.me/submissions/7831e795-3ca4-4bb1-a2ac-60fee827dd3d

import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_base
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_stepD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
open Formalism Formalism.TruncatedSeriesCounting Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
variable {R : Type*} [CommRing R] {G : Type*} [Monoid G] {n : Type} [Fintype n] [DecidableEq n]
variable (N : ℕ)
variable {S : Subring R}
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
theorem _root_.solution (ρ : G →* Matrix n n R) (hS : ∀ g k, (Matrix.charpolyRev (ρ g)).coeff k ∈ S) :
    ∀ j D, 1 ≤ D → N + 1 ≤ D + j → ∀ l : List (R × ℕ × G), Valid S D l → piN N (F ρ l) ∈ SQ N S := by
  intro j
  induction j with
  | zero =>
    intro D hD hj l hl
    rw [base N ρ l (fun L hL => by have := (hl L hL).2; omega)]
    exact (SQ N S).one_mem
  | succ j ih =>
    intro D hD hj l hl
    exact stepD N ρ hS D hD (fun l' hl' => ih (D + 1) (by omega) (by omega) l' hl') _ l hl rfl
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
