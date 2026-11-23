-- Prove2me | solution 1 for Formalism.FG.SolveVAux.phi_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:12.455864+00:00
-- url     : https://prove2.me/submissions/995b2165-a5b6-40ab-b38b-4f5f0bcf7408

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_subst

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
theorem _root_.solution (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) {k : ι → MvPowerSeries τ R}
    (hk : ∀ i, Low 1 (k i)) (j : ι) : Low 1 (phi G g k j) :=
  low_sub (hG j) (low_subst hk (low_mono (by omega) (hg j)))
end Formalism.FG.SolveVAux
