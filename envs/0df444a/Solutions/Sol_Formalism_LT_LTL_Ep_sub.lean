-- Prove2me | solution 1 for Formalism.LT.LTL.Ep_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:45.830801+00:00
-- url     : https://prove2.me/submissions/ef209698-4a27-4740-b33a-ee302ea8cf05

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_inverseIntegralClasses_cc_s_fact

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
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution [Finite ι] (e' : PowerSeries K) (h0 : constantCoeff e' = 0)
    (x y : MvPowerSeries ι K) : Ep e' x - Ep e' y = Ep e' (x - y) := by
  unfold Ep
  rw [MvPowerSeries.subst_sub (MvPowerSeries.hasSubst_of_constantCoeff_zero (inverseIntegralClasses_cc_s_fact e' h0))]
end Formalism.LT.LTL
