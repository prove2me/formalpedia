-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:28.411859+00:00
-- url     : https://prove2.me/submissions/830a3a34-9d39-433f-a04d-9aab90e9d25f

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_hasSubst_of_low

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
namespace Formalism.FG.SolveVAux
theorem _root_.solution {k : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i)) {p : MvPowerSeries ι R}
    (hp : Low 1 p) : Low 1 (subst k p) :=
  (low_one_iff _).2 (constantCoeff_subst_eq_zero (hasSubst_of_low hk)
    (fun i => (low_one_iff _).1 (hk i)) ((low_one_iff _).1 hp))
end Formalism.FG.SolveVAux
