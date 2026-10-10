-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.sum_pearcyVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:40.284988+00:00
-- url     : https://prove2.me/submissions/ce45599f-f24b-4dae-ad81-942aaec71e3c

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.sum_pearcyVec
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E} {w : ℂ} {n : ℕ} (hn : 0 < n)
    (hw : IsPrimitiveRoot w n) (z : ℂ) (y : E) :
    ∑ k ∈ Finset.range n, pearcyVec A (w ^ k * z) n y = (n : ℂ) • y := by

  have hcoef : ∀ m ∈ Finset.range n,
      (∑ k ∈ Finset.range n, (w ^ k * z) ^ m) = if m = 0 then (n : ℂ) else 0 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · have hmn : m < n := Finset.mem_range.mp hm
      have hne : w ^ m ≠ 1 := hw.pow_ne_one_of_pos_of_lt hm0.ne' hmn
      have hsplit : ∑ k ∈ Finset.range n, (w ^ k * z) ^ m
          = z ^ m * ∑ k ∈ Finset.range n, (w ^ m) ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k m]; ring
      have hone : (w ^ m) ^ n = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hw.pow_eq_one, one_pow]
      rw [hsplit, geom_sum_eq hne, hone]
      simp [hm0.ne']
  calc ∑ k ∈ Finset.range n, pearcyVec A (w ^ k * z) n y
      = ∑ m ∈ Finset.range n, (∑ k ∈ Finset.range n, (w ^ k * z) ^ m) • (A ^ m) y := by
        simp only [pearcyVec]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_smul]
    _ = (n : ℂ) • y := by
        rw [Finset.sum_congr rfl (fun m hm => by rw [hcoef m hm])]
        rw [Finset.sum_eq_single 0]
        · simp
        · intro b _ hb; simp [hb]
        · intro hcon; exact absurd (Finset.mem_range.mpr hn) hcon
