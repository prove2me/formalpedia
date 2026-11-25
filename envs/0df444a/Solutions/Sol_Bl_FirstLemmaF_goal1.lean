-- Prove2me | solution 1 for Bl.FirstLemmaF.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:04:13.240192+00:00
-- url     : https://prove2.me/submissions/4e1c4129-e3a6-4ed3-9195-50a54f80401c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.FirstLemmaF
namespace Bl.FirstLemmaF
theorem _root_.solution :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F G : MvPowerSeries.{u_1, 0} σ (PadicComplex p)},
  PI.JetsPhW.IntegralMv.{u_1} F →
    PI.JetsPhW.IntegralMv.{u_1} G → PI.JetsPhW.IntegralMv.{u_1} (HMul.hMul.{u_1, u_1, u_1} F G) := by
  intro p _ σ F G hF hG n
  classical
  unfold PI.JetsPhW.IsIntP
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x : PadicComplex p => ‖x‖ ≤ 1) ?_ ?_ ?_
  · intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  · simp
  · intro x _
    rw [norm_mul]
    exact mul_le_one₀ (hF x.1) (norm_nonneg _) (hG x.2)
end Bl.FirstLemmaF
