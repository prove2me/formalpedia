-- Prove2me | solution 1 for Erdos287.gap_from_weighted_group_moments
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T04:06:20.594176+00:00
-- url     : https://prove2.me/submissions/f6da3aca-fb8b-4d31-bf06-580d010e37e4

import Mathlib
import Theorems.Thm_Erdos287_grouped_prime_occupancy_reduction

open Finset

set_option autoImplicit false

private theorem weighted_occupancy
    (T R : Finset ℕ) (w : ℕ → ℝ) (m : ℕ → ℕ → ℝ)
    (hw : ∀ t ∈ T, 0 ≤ w t) (J P : ℕ)
    (hstrict : (J : ℝ) * (∑ t ∈ T, w t) * (∑ t ∈ T, w t * ∑ s ∈ R, m t s ^ 2) <
      (P : ℝ) * (∑ t ∈ T, w t * ∑ s ∈ R, m t s) ^ 2) :
    ∃ t ∈ T, J < P * (R.filter fun s => m t s ≠ 0).card := by
  classical
  by_contra! hfail
  let p (t : ℕ) := ∑ s ∈ R, m t s
  let q (t : ℕ) := ∑ s ∈ R, m t s ^ 2
  have hq (t : ℕ) : 0 ≤ q t := sum_nonneg (fun _ _ => sq_nonneg _)
  have hsingle (t : ℕ) (ht : t ∈ T) : (P : ℝ) * p t ^ 2 ≤ (J : ℝ) * q t := by
    let S := R.filter fun s => m t s ≠ 0
    have hsum : ∑ s ∈ S, m t s = p t := by
      apply sum_subset (filter_subset _ _)
      intro s hs hdiff
      by_contra hne
      exact hdiff (mem_filter.mpr ⟨hs, hne⟩)
    have hsquares : (∑ s ∈ S, m t s ^ 2) ≤ q t :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    have hcard : (P : ℝ) * (S.card : ℝ) ≤ J := by exact_mod_cast hfail t ht
    have hcs : p t ^ 2 ≤ (S.card : ℝ) * ∑ s ∈ S, m t s ^ 2 := by
      simpa only [hsum, one_pow, sum_const, nsmul_eq_mul, mul_one, one_mul] using
        (sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (m t))
    calc
      (P : ℝ) * p t ^ 2 ≤ (P : ℝ) * ((S.card : ℝ) * ∑ s ∈ S, m t s ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg _)
      _ = (P : ℝ) * (S.card : ℝ) * ∑ s ∈ S, m t s ^ 2 := by ring
      _ ≤ (J : ℝ) * q t :=
        mul_le_mul hcard hsquares (sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hcs :
      (∑ t ∈ T, w t * p t) ^ 2 ≤ (∑ t ∈ T, w t) * ∑ t ∈ T, w t * p t ^ 2 := by
    exact sum_sq_le_sum_mul_sum_of_sq_le_mul T hw
      (fun t ht => mul_nonneg (hw t ht) (sq_nonneg _)) (fun t _ => by ring_nf; exact le_rfl)
  have hsum : (P : ℝ) * (∑ t ∈ T, w t * p t ^ 2) ≤ (J : ℝ) * ∑ t ∈ T, w t * q t := by
    rw [mul_sum, mul_sum]
    apply sum_le_sum
    intro t ht
    have h := mul_le_mul_of_nonneg_left (hsingle t ht) (hw t ht)
    linarith only [mul_left_comm (P : ℝ) (w t) (p t ^ 2),
      mul_left_comm (J : ℝ) (w t) (q t), h]
  have hbound : (P : ℝ) * (∑ t ∈ T, w t * p t) ^ 2 ≤
      (J : ℝ) * (∑ t ∈ T, w t) * ∑ t ∈ T, w t * q t := by
    calc
      (P : ℝ) * (∑ t ∈ T, w t * p t) ^ 2 ≤
          (P : ℝ) * ((∑ t ∈ T, w t) * ∑ t ∈ T, w t * p t ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg _)
      _ = (∑ t ∈ T, w t) * ((P : ℝ) * ∑ t ∈ T, w t * p t ^ 2) := by ring
      _ ≤ (∑ t ∈ T, w t) * ((J : ℝ) * ∑ t ∈ T, w t * q t) :=
        mul_le_mul_of_nonneg_left hsum (sum_nonneg hw)
      _ = _ := by ring
  exact hstrict.not_ge hbound

/-- First and within-group second moments suffice for the Erdős 287 sieve reduction. -/
theorem solution (N K u v : ℕ) (hK : 0 < K) (hu : 0 < u) (huv : u ≤ v)
    (hv : 2 * u ≤ v + 2) (hve : (v : ℝ) < Real.exp 1 * u) :
    ∃ (b : ℕ → ℕ → ℕ) (α β : ℝ) (M₀ : ℕ), 0 < α ∧ α < β ∧
      (∀ s < N, ∀ j < K, 0 < b s j) ∧
      (∀ s r i j, s < N → r < N → i < K → j < K →
        b s i = b r j → s = r ∧ i = j) ∧
      ∀ (k : ℕ) (f : ℕ → ℕ), 2 ≤ k →
        (∀ i, i < k → 1 < f i) →
        (∀ i j, i < j → j < k → f i < f j) →
        (∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) →
        M₀ ≤ f (k - 1) →
        ∀ (T : Finset ℕ) (w : ℕ → ℝ),
          (∀ t ∈ T, α * (f (k - 1) : ℝ) ≤ t ∧ (t : ℝ) ≤ β * f (k - 1)) →
          (∀ t ∈ T, 0 ≤ w t) →
          let m (t s : ℕ) : ℝ :=
            ((Finset.univ.filter fun j : Fin K => Nat.Prime (b s j * t + 1)).card : ℝ)
          let W := ∑ t ∈ T, w t
          let J := ∑ t ∈ T, w t * ∑ s ∈ Finset.range N, m t s
          let Q := ∑ t ∈ T, w t * ∑ s ∈ Finset.range N, m t s ^ 2
          (u : ℝ) * ((N : ℝ) + v) * W * Q < ((u : ℝ) + v) * J ^ 2 →
          ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  classical
  obtain ⟨b, α, β, M₀, hα, hβ, hb, hinj, hgap⟩ :=
    Erdos287.grouped_prime_occupancy_reduction N K u v hK hu huv hv hve
  refine ⟨b, α, β, M₀, hα, hβ, hb, hinj, ?_⟩
  intro k f hk hf hmono hsum hM T w hT hw m W J Q hstrict
  have hh : ((u * (N + v) : ℕ) : ℝ) * W * Q < ((u + v : ℕ) : ℝ) * J ^ 2 := by
    push_cast
    exact hstrict
  obtain ⟨t, ht, hcard⟩ := weighted_occupancy T (range N) w m hw (u * (N + v)) (u + v) hh
  have heq : (range N).filter (fun s => m t s ≠ 0) =
      (range N).filter (fun s => ∃ j : Fin K, Nat.Prime (b s j * t + 1)) := by
    ext s
    simp only [mem_filter]
    apply and_congr_right
    intro _
    dsimp [m]
    simp only [Nat.cast_eq_zero]
    exact Finset.card_ne_zero.trans (by simp [Finset.Nonempty])
  exact hgap k f hk hf hmono hsum hM t (hT t ht).1 (hT t ht).2 (heq ▸ hcard)

