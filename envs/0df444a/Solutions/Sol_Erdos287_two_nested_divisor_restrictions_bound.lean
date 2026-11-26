-- Prove2me | solution 1 for Erdos287.two_nested_divisor_restrictions_bound
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T15:15:53.285931+00:00
-- url     : https://prove2.me/submissions/8c6ab190-4b0c-464c-892f-2e7b3b5e8bb2

import Mathlib

open Finset

set_option autoImplicit false

private theorem sum_on_multiples_le
    (N b : ℕ) (hb : 0 < b) (S : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hmul : ∀ a b, w (a * b) ≤ w a * w b) :
    (∑ s ∈ S.filter (b ∣ ·), w s) ≤ w b * ∑ t ∈ Icc 1 N, w t := by
  let T := (Icc 1 N).filter fun t => b * t ∈ S
  have himage : T.image (b * ·) = S.filter (b ∣ ·) := by
    ext s
    simp only [mem_image, mem_filter, T]
    constructor
    · rintro ⟨t, ⟨_, ht⟩, rfl⟩
      exact ⟨ht, dvd_mul_right b t⟩
    · rintro ⟨hs, ⟨t, rfl⟩⟩
      have hst := mem_Icc.mp (hS hs)
      have ht : 1 ≤ t := by
        by_contra! h
        have ht0 : t = 0 := by omega
        simp [ht0] at hst
      have htn : t ≤ N := calc
        t = 1 * t := by simp
        _ ≤ b * t := Nat.mul_le_mul_right t (by omega)
        _ ≤ N := hst.2
      exact ⟨t, ⟨mem_Icc.mpr ⟨ht, htn⟩, hs⟩, rfl⟩
  rw [← himage, sum_image (fun _ _ _ _ h => (Nat.mul_left_cancel_iff hb).mp h)]
  calc
    (∑ t ∈ T, w (b * t)) ≤ ∑ t ∈ T, w b * w t :=
      sum_le_sum fun t _ => hmul b t
    _ = w b * ∑ t ∈ T, w t := by rw [mul_sum]
    _ ≤ w b * ∑ t ∈ Icc 1 N, w t :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun t _ _ => hw t)) (hw b)

private theorem swap_divisor_sum (S K : Finset ℕ) (a b : ℕ → ℝ) :
    (∑ s ∈ S, a s * ∑ k ∈ K.filter (· ∣ s), b k) =
    ∑ k ∈ K, b k * ∑ s ∈ S.filter (k ∣ ·), a s := by
  simp only [sum_filter, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro s _
  by_cases h : k ∣ s <;> simp [h, mul_comm]

/-- Two restrictions to divisors cost at most the square of the total
submultiplicative weight. -/
theorem solution (N : ℕ) (S K F : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 N) (hK : K ⊆ Finset.Icc 1 N) (hF : F ⊆ Finset.Icc 1 N)
    (w z : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hz : ∀ n, 0 ≤ z n)
    (hmul : ∀ a b, w (a * b) ≤ w a * w b) :
    (∑ s ∈ S, w s * ∑ k ∈ K.filter (· ∣ s), ∑ f ∈ F.filter (· ∣ k), z f) ≤
    (∑ n ∈ Finset.Icc 1 N, w n) ^ 2 * ∑ f ∈ F, w f * z f := by
  let C := ∑ n ∈ Icc 1 N, w n
  let u (k : ℕ) := ∑ f ∈ F.filter (· ∣ k), z f
  have hC : 0 ≤ C := sum_nonneg fun n _ => hw n
  calc
    (∑ s ∈ S, w s * ∑ k ∈ K.filter (· ∣ s), u k) =
        ∑ k ∈ K, u k * ∑ s ∈ S.filter (k ∣ ·), w s := swap_divisor_sum S K w u
    _ ≤ ∑ k ∈ K, u k * (w k * C) := by
      apply sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (sum_on_multiples_le N k (mem_Icc.mp (hK hk)).1 S hS w hw hmul)
        (sum_nonneg fun f _ => hz f)
    _ = C * ∑ k ∈ K, w k * u k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    _ = C * ∑ f ∈ F, z f * ∑ k ∈ K.filter (f ∣ ·), w k := by
      rw [show (∑ k ∈ K, w k * u k) = _ from swap_divisor_sum K F w z]
    _ ≤ C * ∑ f ∈ F, z f * (w f * C) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply sum_le_sum
      intro f hf
      exact mul_le_mul_of_nonneg_left
        (sum_on_multiples_le N f (mem_Icc.mp (hF hf)).1 K hK w hw hmul) (hz f)
    _ = C ^ 2 * ∑ f ∈ F, w f * z f := by
      rw [mul_sum, mul_sum]
      apply sum_congr rfl
      intro f _
      ring

