-- Prove2me | solution 1 for Formalism.LT.LTL.coeff_corr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:34:01.742881+00:00
-- url     : https://prove2.me/submissions/dc6919fc-8244-4fd1-b22d-36ab52a2f099

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
namespace Formalism.LT.LTL
theorem _root_.solution (e e' : PowerSeries K) (π : K) (N : ℕ) (P : MvPowerSeries ι K)
    (d : ι →₀ ℕ) : MvPowerSeries.coeff d (corr e e' π N P) =
      if d.degree = N + 1 then MvPowerSeries.coeff d (Ldef e e' P) / (π - π ^ (N + 1)) else 0 :=
  rfl
end Formalism.LT.LTL
