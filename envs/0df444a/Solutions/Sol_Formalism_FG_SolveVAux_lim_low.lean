-- Prove2me | solution 1 for Formalism.FG.SolveVAux.lim_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:38:56.310293+00:00
-- url     : https://prove2.me/submissions/ee45b69d-3b35-49bf-a736-07a48bc45fae

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_seq_low
import Theorems.Thm_Formalism_FG_SolveVAux_lim_close

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
theorem _root_.solution (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (i : ι) :
    Low 1 (lim G g i) := by
  have := low_add (lim_close hG hg 1 i) (seq_low hG hg 1 i)
  rwa [sub_add_cancel] at this
end Formalism.FG.SolveVAux
