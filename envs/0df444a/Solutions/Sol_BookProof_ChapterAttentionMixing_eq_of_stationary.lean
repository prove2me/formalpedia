-- Prove2me | solution 1 for BookProof.ChapterAttentionMixing.eq_of_stationary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:09:00.940497+00:00
-- url     : https://prove2.me/submissions/ebc13117-a86b-4b91-8bbc-98a5eb6a9ee3

-- Generated from ChapterAttentionMixing.lean — solution of BookProof.ChapterAttentionMixing.eq_of_stationary
import Mathlib
import Definitions.Def_ChapterAttentionMixing
import Theorems.Thm_BookProof_ChapterAttentionMarkov_l1dist_nonneg
import Theorems.Thm_BookProof_ChapterAttentionMarkov_l1dist_push_le_of_min
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
    (hpos : 0 < eps) (i : Fin m) (hfp : push P p = p) (hfq : push P q = q) : p = q := by

  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast i.pos
  have hc1 : 1 - (m : ℝ) * eps < 1 := by nlinarith
  have hstep := l1dist_push_le_of_min hP hmin hp hq
  rw [hfp, hfq] at hstep
  have hnn : 0 ≤ l1dist p q := l1dist_nonneg p q
  have hzero : l1dist p q = 0 := by nlinarith
  funext j
  have habs : |p j - q j| = 0 := by
    refine le_antisymm ?_ (abs_nonneg _)
    calc |p j - q j| ≤ ∑ l, |p l - q l| :=
          Finset.single_le_sum (f := fun l => |p l - q l|) (fun l _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ = 0 := hzero
  have := abs_eq_zero.mp habs
  linarith [sub_eq_zero.mp this]
