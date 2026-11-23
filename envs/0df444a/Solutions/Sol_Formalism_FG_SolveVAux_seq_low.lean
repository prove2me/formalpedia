-- Prove2me | solution 1 for Formalism.FG.SolveVAux.seq_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:15.429645+00:00
-- url     : https://prove2.me/submissions/20164a8e-1f06-4682-bcd1-80c1a833cc86

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_of_zero
import Theorems.Thm_Formalism_FG_SolveVAux_seq_succ
import Theorems.Thm_Formalism_FG_SolveVAux_phi_low

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
    Low 1 (seq G g n i) := by
  induction n generalizing i with
  | zero => exact low_of_zero _
  | succ n ih => rw [seq_succ]; exact phi_low hG hg ih i
end Formalism.FG.SolveVAux
