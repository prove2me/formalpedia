-- Prove2me | solution 1 for BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:08:59.573008+00:00
-- url     : https://prove2.me/submissions/880837c3-e514-4521-ae13-a676cbd72b81

-- Generated from ChapterAttentionMixing.lean — solution of BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter
import Mathlib
import Definitions.Def_ChapterAttentionMixing
import Theorems.Thm_BookProof_ChapterAttentionMixing_mul_min_le_one
import Theorems.Thm_BookProof_ChapterAttentionMixing_l1dist_pushIter_le
import Theorems.Thm_BookProof_ChapterAttentionMarkov_l1dist_nonneg
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov
open BookProof.ChapterAttentionMixing



open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ}
    (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : IsProb q)
    (hpos : 0 < eps) (i : Fin m) :
    Tendsto (fun n => l1dist (pushIter P n p) (pushIter P n q)) atTop (𝓝 0) := by

  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast i.pos
  have hc0 : 0 ≤ 1 - (m : ℝ) * eps := by
    have := mul_min_le_one hP hmin i
    linarith
  have hc1 : 1 - (m : ℝ) * eps < 1 := by nlinarith
  have hlim : Tendsto (fun n : ℕ => (1 - (m : ℝ) * eps) ^ n * l1dist p q) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
    simpa using this.mul_const (l1dist p q)
  refine squeeze_zero (fun n => l1dist_nonneg _ _) (fun n => ?_) hlim
  exact l1dist_pushIter_le hP hmin hp hq n
