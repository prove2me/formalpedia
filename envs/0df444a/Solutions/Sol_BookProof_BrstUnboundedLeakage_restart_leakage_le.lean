-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.restart_leakage_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-22T17:04:36.069991+00:00
-- url     : https://prove2.me/submissions/60587922-58ee-467f-91d0-37abf6a4c5b7

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.restart_leakage_le
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Theorems.Thm_BookProof_BrstUnboundedLeakage_truncation_leakage_le
import Theorems.Thm_BookProof_BrstUnboundedLeakage_norm_restartIter
import Theorems.Thm_BookProof_BrstLeakage_leakageIter_succ
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent
open BookProof.BrstLeakage

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)
variable (Vs : ℕ → Submodule ℂ H) [∀ i, FiniteDimensional ℂ (Vs i)] (hVs : ∀ i, Vs i ≤ T.domain)

set_option maxHeartbeats 1000000 in

theorem solution {Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (τ : ℝ) (hτ : 0 ≤ τ) (x : H) (D : ℝ)
    (hret : ∀ i, leakageIter (restartGen T Vs hVs) τ x i ∈ Vs i)
    (hD : ∀ i, ‖truncDefect T (Vs i) (hVs i)‖ ≤ D) :
    ∀ n : ℕ, ‖Om (leakageIter (restartGen T Vs hVs) τ x n)‖
      ≤ ‖Om x‖ + n * (‖Om‖ * (D * ‖x‖ * τ))
  | 0 => by simp [leakageIter]
  | n + 1 => by
      have hxn : ‖leakageIter (restartGen T Vs hVs) τ x n‖ = ‖x‖ :=
        norm_restartIter T Vs hVs τ x n
      have hstep := truncation_leakage_le T (Vs n) (hVs n) (Om := Om) hcomm τ hτ (hret n)
      have hmono : ‖Om‖ * (‖truncDefect T (Vs n) (hVs n)‖
            * ‖leakageIter (restartGen T Vs hVs) τ x n‖ * τ)
          ≤ ‖Om‖ * (D * ‖x‖ * τ) := by
        rw [hxn]
        gcongr
        exact hD n
      have hsucc : ‖Om (leakageIter (restartGen T Vs hVs) τ x (n + 1))‖
          ≤ ‖Om (leakageIter (restartGen T Vs hVs) τ x n)‖ + ‖Om‖ * (D * ‖x‖ * τ) := by
        rw [leakageIter_succ]
        exact hstep.trans (by gcongr)
      have hind := solution hcomm τ hτ x D hret hD n
      have hcast : ((n : ℝ) + 1) * (‖Om‖ * (D * ‖x‖ * τ))
          = (n : ℝ) * (‖Om‖ * (D * ‖x‖ * τ)) + ‖Om‖ * (D * ‖x‖ * τ) := by ring
      push_cast
      rw [hcast]
      linarith
