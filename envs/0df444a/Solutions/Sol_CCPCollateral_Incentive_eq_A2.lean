-- Prove2me | solution 1 for CCPCollateral.Incentive.eq_A2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:47:09.275579+00:00
-- url     : https://prove2.me/submissions/9cd99f15-8287-4cdb-a1cf-93647667601b

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting
open CCPCollateral.Incentive

theorem solution(m : Params) (hm : Standing m) :
    ∀ (g : ℕ) (I F : ℝ),
      m.V Action.r g I F ≤ m.V Action.s g I F ↔
        m.D - I - F + m.X g I F ≤ (m.Accp - I - F) * m.pledge := by
  intro g I F
  have hk : 0 < m.pc * (m.qr - m.qs) := mul_pos hm.pc_mem.1 (by linarith [hm.cond1.2.1])
  have hp : m.pledge * (m.pc * (m.qr - m.qs)) = (1 - m.qs) * m.Rs - (1 - m.qr) * m.Rr := by
    unfold Params.pledge
    rw [div_mul_cancel₀ _ hk.ne']
    simp only [Params.mu, Params.q, Params.R]
  have key : m.V Action.s g I F - m.V Action.r g I F
      = m.pc * (m.qr - m.qs) * ((m.Accp - I - F) * m.pledge - (m.D - I - F + m.X g I F)) := by
    unfold Params.V Params.q Params.R
    linear_combination (-(m.Accp - I - F)) * hp
  rw [← sub_nonneg, key, mul_nonneg_iff_of_pos_left hk, sub_nonneg]
