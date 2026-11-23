-- Prove2me | solution 1 for Formalism.FG.InvIntVAux.low_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:58.994144+00:00
-- url     : https://prove2.me/submissions/20194e68-28fa-45e9-a380-ab27c2944539

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
theorem _root_.solution {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) : Low 1 x := by
  intro d hd
  have h0 : d = 0 := by
    first
      | exact (Finsupp.degree_eq_zero_iff d).1 (by omega)
      | exact Finsupp.degree_eq_zero_iff.1 (by omega)
      | simpa using (show d.degree = 0 by omega)
  subst h0
  first
    | exact hx
    | simpa using hx
end Formalism.FG.InvIntVAux
