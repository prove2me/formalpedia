-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.leakage_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:47:52.669997+00:00
-- url     : https://prove2.me/submissions/3124c90b-2638-4df1-a32e-b99e148a3de0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.leakage_le
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Theorems.Thm_BookProof_BrstUnboundedLeakage_norm_flow_sub_stoneU_le
import Theorems.Thm_BookProof_BrstUnboundedLeakage_norm_omega_stoneU_eq
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution {B Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (t : ℝ) (ht : 0 ≤ t) (x : H) (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖T.op ⟨flow B s x, hdom s⟩ - B (flow B s x)‖ ≤ K) :
    ‖Om (flow B t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (K * t) := by

  have hdiff := norm_flow_sub_stoneU_le T t ht x hdom K hK
  have hsplit : Om (flow B t x)
      = Om (T.stoneU t x) + Om (flow B t x - T.stoneU t x) := by
    rw [map_sub]; abel
  have h1 : ‖Om (T.stoneU t x)‖ = ‖Om x‖ := norm_omega_stoneU_eq T hcomm t x
  calc ‖Om (flow B t x)‖
      ≤ ‖Om (T.stoneU t x)‖ + ‖Om (flow B t x - T.stoneU t x)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖Om x‖ + ‖Om‖ * (K * t) := by
        rw [h1]
        gcongr
        exact (Om.le_opNorm _).trans (by gcongr)
