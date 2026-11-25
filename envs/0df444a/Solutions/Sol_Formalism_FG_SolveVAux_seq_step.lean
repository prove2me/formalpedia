-- Prove2me | solution 1 for Formalism.FG.SolveVAux.seq_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:49.407731+00:00
-- url     : https://prove2.me/submissions/2a580025-005b-414d-86bf-9475087272d5

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_FG_SolveVAux_seq_succ
import Theorems.Thm_Formalism_FG_SolveVAux_phi_sub
import Theorems.Thm_Formalism_FG_SolveVAux_seq_low

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
theorem _root_.solution (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n : ℕ) (i : ι) :
    Low n (seq G g (n + 1) i - seq G g n i) := by
  induction n generalizing i with
  | zero => exact low_zero _
  | succ n ih =>
    have := phi_sub (G := G) hg (seq_low hG hg (n + 1)) (seq_low hG hg n) ih i
    rwa [← seq_succ, ← seq_succ] at this
end Formalism.FG.SolveVAux
