-- Prove2me | solution 1 for Formalism.FG.SolveVAux.seq_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:20:03.448134+00:00
-- url     : https://prove2.me/submissions/ec8c766e-bcc1-412c-9128-f3866b00ec48

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_of_zero
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_seq_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι] {τ : Type w}
variable {G : ι → MvPowerSeries τ R} {g : ι → MvPowerSeries ι R}
namespace Formalism.FG.SolveVAux
theorem _root_.solution (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n m : ℕ) (hnm : n ≤ m)
    (i : ι) : Low n (seq G g m i - seq G g n i) := by
  induction m, hnm using Nat.le_induction with
  | base => rw [sub_self]; exact low_of_zero _
  | succ m hnm ih =>
    have e : seq G g (m + 1) i - seq G g n i =
        (seq G g (m + 1) i - seq G g m i) + (seq G g m i - seq G g n i) := by abel
    rw [e]
    exact low_add (low_mono hnm (seq_step hG hg m i)) ih
end Formalism.FG.SolveVAux
