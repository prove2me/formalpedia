-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_aligned_dyadic_values_card_uniform_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:23:25.703267+00:00
-- url     : https://prove2.me/submissions/ca655204-87df-40de-8f16-5eeeb8fab632

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_aligned_dyadic_active_count_ae_finite
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators

namespace AV_b93e

theorem card_image_le (f : ℕ → ℝ) (hf : ∀ i j, i ≤ j → f i ≤ f j) : ∀ m : ℕ,
    ((Finset.range (m + 1)).image f).card ≤
      1 + ∑ i ∈ Finset.range m, ite (f i < f (i + 1)) (1 : ℕ) 0 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.range_add_one (n := m + 1), Finset.image_insert, Finset.sum_range_succ]
    by_cases h : f m < f (m + 1)
    · rw [if_pos h]
      exact (Finset.card_insert_le _ _).trans (by omega)
    · rw [if_neg h]
      have he : f (m + 1) = f m := le_antisymm (not_lt.1 h) (hf _ _ (by omega))
      have hmem : f (m + 1) ∈ (Finset.range (m + 1)).image f :=
        Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), he.symm⟩
      rw [Finset.insert_eq_of_mem hmem]; omega

end AV_b93e

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℕ → ℝ≥0) (T : ℝ)
    (hAlign : ∀ n i : ℕ, grid (n + 1) (2 * i) = grid n i)
    (hGridMono : ∀ n, Monotone (grid n))
    (hMesh : ∀ n i : ℕ, i < 2 ^ n →
      (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ) =
        T / ((2 ^ n : ℕ) : ℝ))) :
    ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ n : ℕ,
      ((Finset.range (2 ^ n + 1)).image (fun i =>
        (grid n i : ℝ) * X.drift - X.X (grid n i) ω)).card ≤ K := by
  have h1 := AvramDividend.Classical.bv_actual_aligned_dyadic_active_count_ae_finite X hBV hFinite
    grid T hAlign (fun n i _ => hGridMono n (Nat.le_succ i)) hMesh
  have h2 := AvramDividend.Classical.bv_actual_levy_residual_ae_monotone_all_times X hBV
  filter_upwards [h1, h2] with ω hK hmono
  obtain ⟨K, hK⟩ := hK
  refine ⟨1 + K, fun n => ?_⟩
  refine (AV_b93e.card_image_le (fun i => (grid n i : ℝ) * X.drift - X.X (grid n i) ω)
    (fun i j hij => hmono (hGridMono n hij)) (2 ^ n)).trans ?_
  have := hK n
  omega
