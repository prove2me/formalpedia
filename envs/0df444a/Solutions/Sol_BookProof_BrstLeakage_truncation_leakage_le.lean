-- Prove2me | solution 1 for BookProof.BrstLeakage.truncation_leakage_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:46:15.486318+00:00
-- url     : https://prove2.me/submissions/6d84ecc1-6843-4e8e-b60e-d0c25405e923

-- Generated from ChapterBrstTruncationLeakage.lean — solution of BookProof.BrstLeakage.truncation_leakage_le
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
import Theorems.Thm_BookProof_BrstLeakage_norm_flow_apply
import Theorems.Thm_BookProof_BrstLeakage_leakage_le
import Theorems.Thm_BookProof_BrstLeakage_truncGen_isSelfAdjoint
import Theorems.Thm_BookProof_BrstLeakage_flow_truncGen_mem
open BookProof.BrstLeakage



open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {P H Om : E →L[ℂ] E} (hPi : IsIdempotentElem P)
    (hPs : IsSelfAdjoint P) (hH : IsSelfAdjoint H) (hcomm : Commute H Om)
    (t : ℝ) (ht : 0 ≤ t) {x : E} (hx : P x = x) :
    ‖Om (flow (truncGen P H) t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (‖(1 - P) * H * P‖ * ‖x‖ * t) := by

  have hB : IsSelfAdjoint (truncGen P H) := truncGen_isSelfAdjoint hPs hH
  have hK : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖(H - truncGen P H) (flow (truncGen P H) s x)‖ ≤ ‖(1 - P) * H * P‖ * ‖x‖ := by
    intro s _
    set y : E := flow (truncGen P H) s x with hy
    have hPy : P y = y := flow_truncGen_mem hPi s hx
    have hrw : (H - truncGen P H) y = ((1 - P) * H * P) y := by
      have : ((1 - P) * H * P) y = H (P y) - P (H (P y)) := by
        simp [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply]
      rw [this, hPy]
      simp [truncGen, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, hPy]
    rw [hrw]
    calc ‖((1 - P) * H * P) y‖ ≤ ‖(1 - P) * H * P‖ * ‖y‖ := ((1 - P) * H * P).le_opNorm _
      _ = ‖(1 - P) * H * P‖ * ‖x‖ := by rw [hy, norm_flow_apply hB]
  have := leakage_le hH hcomm t ht x (‖(1 - P) * H * P‖ * ‖x‖) hK
  calc ‖Om (flow (truncGen P H) t x)‖
      ≤ ‖Om x‖ + ‖Om‖ * (‖(1 - P) * H * P‖ * ‖x‖ * t) := by
        simpa [mul_assoc] using this
