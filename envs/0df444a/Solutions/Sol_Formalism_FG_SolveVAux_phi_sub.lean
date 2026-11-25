-- Prove2me | solution 1 for Formalism.FG.SolveVAux.phi_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:04:01.480804+00:00
-- url     : https://prove2.me/submissions/5e4ec01d-edee-4958-b39d-5375918b2156

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_subst_sub

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
theorem _root_.solution (hg : ∀ j, Low 2 (g j)) {M : ℕ} {k k' : ι → MvPowerSeries τ R}
    (hk : ∀ i, Low 1 (k i)) (hk' : ∀ i, Low 1 (k' i)) (hkk : ∀ i, Low M (k i - k' i)) (j : ι) :
    Low (M + 1) (phi G g k j - phi G g k' j) := by
  have e : phi G g k j - phi G g k' j = subst k' (g j) - subst k (g j) := by
    simp only [phi]; abel
  rw [e]
  refine low_subst_sub hk' hk (fun i => ?_) (hg j)
  have := low_neg (hkk i)
  rwa [neg_sub] at this
end Formalism.FG.SolveVAux
