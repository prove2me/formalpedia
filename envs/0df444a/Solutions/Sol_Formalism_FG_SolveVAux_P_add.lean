-- Prove2me | solution 1 for Formalism.FG.SolveVAux.P_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:18.795694+00:00
-- url     : https://prove2.me/submissions/21e8364f-5205-484b-b37f-6a3875158d7f

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV

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
variable {R : Type u} [CommRing R] {ι : Type v} {τ : Type w}
namespace Formalism.FG.SolveVAux
theorem _root_.solution (k : ι → MvPowerSeries τ R) (e₁ e₂ : ι →₀ ℕ) :
    P k (e₁ + e₂) = P k e₁ * P k e₂ :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
end Formalism.FG.SolveVAux
