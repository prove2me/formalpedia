-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutTargetRank_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:38.108624+00:00
-- url     : https://prove2.me/submissions/1702404b-d240-4e3e-859b-dd7a781957e0

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Theorems.Thm_FirstPassageLinearTransport_timeoutTargetRank_pos_of_half_lt
import Theorems.Thm_FirstPassageLinearTransport_timeoutTargetRank_lt_parent
import Theorems.Thm_FirstPassageLinearTransport_eventually_movingLow_admissible
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingLowRatio


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Topology
namespace FirstPassageLinearTransport
theorem _root_.solution
    {K₀ : ℝ} (hK₀ : 0 < K₀) :
    ∀ᶠ L : ℕ in atTop, ∀ m : ℕ, L ≤ m →
      0 < timeoutTargetRank K₀ L m ∧
        timeoutTargetRank K₀ L m < m := by
  have hhalf : ∀ᶠ L : ℕ in atTop,
      (1 / 2 : ℝ) < movingLowRatio K₀ L :=
    (tendsto_movingLowRatio K₀).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hadm := eventually_movingLow_admissible hK₀
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hhalf, hadm, eventually_ge_atTop (5 : ℕ)]
    with L hhalf hadm hL
  intro m hLm
  exact ⟨timeoutTargetRank_pos_of_half_lt hhalf (hL.trans hLm),
    timeoutTargetRank_lt_parent hadm.2.2.1.le hadm.2.2.2.1
      (by omega)⟩
end FirstPassageLinearTransport
