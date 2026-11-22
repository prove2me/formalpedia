-- Prove2me | solution 1 for Formalism.LT.InvIntP.agree_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:51.420945+00:00
-- url     : https://prove2.me/submissions/7d9cd80a-1d39-442b-a4c6-be6f9b2bd04c

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT Formalism.LT.InvIntP
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K] {ι : Type v}
namespace Formalism.LT.InvIntP
theorem _root_.solution [Finite ι] (g : PowerSeries K) {N : ℕ} {a b : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) (hb0 : MvPowerSeries.constantCoeff b = 0)
    (hab : Agree N a b) : Agree N (g.subst a) (g.subst b) := by
  exact Agree.subst (f := g) (f' := g) (a := fun _ : Unit => a) (a' := fun _ : Unit => b)
    (fun _ => ha0) (fun _ => hb0) (fun _ _ => rfl) (fun _ => hab)
end Formalism.LT.InvIntP
