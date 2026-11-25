-- Prove2me | solution 1 for Formalism.FG.SolveVAux.lim_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:27:16.663034+00:00
-- url     : https://prove2.me/submissions/14ba88d5-f4b1-427f-a889-4f63fbe4b7ff

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_seq_stable
import Theorems.Thm_Formalism_FG_SolveVAux_coeff_lim

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
    Low n (lim G g i - seq G g n i) := by
  intro d hd
  have := seq_stable hG hg (d.degree + 1) n (by omega) i d (by omega)
  rw [map_sub, sub_eq_zero] at this
  rw [map_sub, coeff_lim, this, sub_self]
end Formalism.FG.SolveVAux
