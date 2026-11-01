-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_dyadic_residual_values_one_finite_set
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:16:19.434113+00:00
-- url     : https://prove2.me/submissions/3517c73d-46eb-4f62-9fb6-eb2d65781a3a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_aligned_dyadic_values_card_uniform_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

namespace AV_Wave4_04A

private theorem nested_finsets_bounded_common
    {α : Type*} [DecidableEq α]
    (s : ℕ → Finset α)
    (hmono : Monotone s)
    (K : ℕ) (hcard : ∀ n, (s n).card ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, s n ⊆ s N := by
  let U : Set ℕ := Set.range (fun n => (s n).card)
  have hne : U.Nonempty := ⟨(s 0).card, ⟨0, rfl⟩⟩
  have hbd : BddAbove U := by
    refine ⟨K, ?_⟩
    rintro k ⟨n, rfl⟩
    exact hcard n
  obtain ⟨N, hN⟩ : ∃ N, (s N).card = sSup U := Nat.sSup_mem hne hbd
  refine ⟨N, ?_⟩
  intro n
  have hsubset : s N ⊆ s (max n N) := hmono (le_max_right n N)
  have hmaxcard : (s (max n N)).card ≤ (s N).card := by
    rw [hN]
    exact le_csSup hbd ⟨max n N, rfl⟩
  have heq : s N = s (max n N) :=
    Finset.eq_of_subset_of_card_le hsubset hmaxcard
  simpa [← heq] using (hmono (le_max_left n N))

end AV_Wave4_04A

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
    ∀ᵐ ω ∂P, ∃ S : Finset ℝ, ∀ (n i : ℕ), i ≤ 2 ^ n →
      (grid n i : ℝ) * X.drift - X.X (grid n i) ω ∈ S := by
  classical
  filter_upwards
    [bv_actual_aligned_dyadic_values_card_uniform_ws01b
      X hBV hFinite grid T hAlign hGridMono hMesh]
    with ω hω
  obtain ⟨K, hK⟩ := hω
  let A : ℕ → Finset ℝ := fun n =>
    (Finset.range (2 ^ n + 1)).image
      (fun i => (grid n i : ℝ) * X.drift - X.X (grid n i) ω)
  have hstep : ∀ n, A n ⊆ A (n + 1) := by
    intro n x hx
    change x ∈ (Finset.range (2 ^ n + 1)).image
      (fun i => (grid n i : ℝ) * X.drift - X.X (grid n i) ω) at hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    change (grid n i : ℝ) * X.drift - X.X (grid n i) ω ∈
      (Finset.range (2 ^ (n + 1) + 1)).image
      (fun j => (grid (n + 1) j : ℝ) * X.drift -
        X.X (grid (n + 1) j) ω)
    apply Finset.mem_image.mpr
    refine ⟨2 * i, ?_, ?_⟩
    · simp only [Finset.mem_range] at hi ⊢
      simp only [pow_succ]
      omega
    · simp only [hAlign n i]
  have hmono : Monotone A := monotone_nat_of_le_succ hstep
  have hcard : ∀ n, (A n).card ≤ K := hK
  obtain ⟨N, hN⟩ :=
    AV_Wave4_04A.nested_finsets_bounded_common A hmono K hcard
  refine ⟨A N, ?_⟩
  intro n i hi
  apply hN n
  change (grid n i : ℝ) * X.drift - X.X (grid n i) ω ∈
    (Finset.range (2 ^ n + 1)).image
      (fun j => (grid n j : ℝ) * X.drift - X.X (grid n j) ω)
  exact Finset.mem_image.mpr
    ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
