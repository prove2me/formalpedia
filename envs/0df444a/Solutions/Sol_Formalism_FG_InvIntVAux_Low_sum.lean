-- Prove2me | solution 1 for Formalism.FG.InvIntVAux.Low.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:59:01.862412+00:00
-- url     : https://prove2.me/submissions/0e92f1fd-7869-479e-9d3e-1df89e5dc2c2

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV

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
open Formalism Formalism.FG Formalism.FG.InvIntVAux
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K]
variable {σ : Type*}
namespace Formalism.FG.InvIntVAux
namespace Low
theorem _root_.solution {α : Type*} {m : ℕ} (s : Finset α) (x : α → MvPowerSeries σ K)
    (h : ∀ a ∈ s, Low m (x a)) : Low m (∑ a ∈ s, x a) := by
  intro d hd
  rw [map_sum]
  exact Finset.sum_eq_zero fun a ha => h a ha d hd
end Low
end Formalism.FG.InvIntVAux
