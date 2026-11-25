-- Prove2me | solution 1 for Bl.FirstLemmaG.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:04:16.104549+00:00
-- url     : https://prove2.me/submissions/5704558f-22fb-4da4-85d7-70ed8a6291fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.FirstLemmaG
namespace Bl.FirstLemmaG
theorem _root_.solution :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries.{u_1, 0} σ (PadicComplex p)} (i : σ),
  PI.JetsPhW.IntegralMv.{u_1} F →
    PI.JetsPhW.IntegralMv.{u_1}
      (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} (MvPowerSeries.pderiv.{u_1, 0} (PadicComplex p) i) F) := by
  intro p _ σ F i hF n
  show ‖MvPowerSeries.coeff n (MvPowerSeries.pderiv (PadicComplex p) i F)‖ ≤ 1
  rw [MvPowerSeries.coeff_pderiv, norm_mul]
  have h1 : ‖MvPowerSeries.coeff (n + Finsupp.single i 1) F‖ ≤ 1 := hF _
  have h2 : ‖((n i : PadicComplex p) + 1)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one (PadicComplex p) (n i + 1)
    rwa [Nat.cast_succ] at this
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1
end Bl.FirstLemmaG
