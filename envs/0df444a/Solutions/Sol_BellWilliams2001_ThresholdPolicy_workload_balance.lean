-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.workload_balance
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:57:06.586193+00:00
-- url     : https://prove2.me/submissions/0665c34b-4208-44a9-9a5c-98d4837a3035

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Workload

open BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 650000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (ω : Ω) (t : ℝ) :
    M.workload n T ω t = M.serverTwoInput n T ω t + M.muR n 1 * M.Ihat n T ω t 1 := by
  have hR : M.r n ≠ 0 := (zero_lt_one.trans_le (M.r_ge n)).ne'
  have hR2 : M.r n ^ 2 ≠ 0 := pow_ne_zero 2 hR
  have hMu1 := (M.muR_pos n 1).ne'
  have hMu2 := (M.muR_pos n 2).ne'
  have hFrac : (M.lam 0 - M.mu 0) / M.mu 1 + M.lam 1 / M.mu 2 = 1 := by
    linarith [M.a31_ii]
  have hc (j : Fin 3) : M.r n ^ 2 * (T ω j (M.r n ^ 2 * t) / M.r n ^ 2) =
      T ω j (M.r n ^ 2 * t) := mul_div_cancel₀ _ hR2
  simp only [SystemSequence.workload, SystemSequence.serverTwoInput,
    SystemSequence.workloadInput, SystemSequence.poolingWeight, SystemSequence.Xhat,
    SystemSequence.Ahat, SystemSequence.Shat, SystemSequence.driftR, SystemSequence.Tbar,
    SystemSequence.Qhat, SystemSequence.queue, SystemSequence.Ihat, SystemSequence.idle,
    if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, hc]
  rw [show M.lam 1 / M.mu 2 = 1 - (M.lam 0 - M.mu 0) / M.mu 1 from M.a31_ii.symm]
  field_simp
  <;> ring
