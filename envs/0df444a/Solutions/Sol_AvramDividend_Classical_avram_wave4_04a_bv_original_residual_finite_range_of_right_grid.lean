-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_original_residual_finite_range_of_right_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:19:58.878321+00:00
-- url     : https://prove2.me/submissions/3eab1360-6a76-4140-a3a0-72d4b73d9d50

import Mathlib
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_aligned_dyadic_values_card_uniform_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

namespace AV_Wave4_04A_AllTime

private theorem nested_finsets_common
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

end AV_Wave4_04A_AllTime

/--
Original-path finite-activity BV residual has a finite range on a finite horizon,
provided the aligned dyadic grid approaches every time from the right.
The right-approximation hypothesis is deliberately explicit: the predecessor
finite-grid theorem alone does not anchor its arbitrary dyadic grid at zero.
The proof identifies original-path residual values without constructing a replacement Lévy process.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℕ → ℝ≥0) (T : ℝ≥0)
    (hAlign : ∀ n i : ℕ, grid (n + 1) (2 * i) = grid n i)
    (hGridMono : ∀ n, Monotone (grid n))
    (hMesh : ∀ n i : ℕ, i < 2 ^ n →
      (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ) =
        (T : ℝ) / ((2 ^ n : ℕ) : ℝ)))
    (hRightCover : ∀ t : ℝ≥0, t ≤ T →
      ∃ index : ℕ → ℕ,
        (∀ n, index n ≤ 2 ^ n) ∧
        (∀ n, t ≤ grid n (index n)) ∧
        Tendsto (fun n => grid n (index n)) atTop (nhds t)) :
    ∀ᵐ ω ∂P, ∃ S : Finset ℝ, ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) * X.drift - X.X t ω ∈ S := by
  classical
  filter_upwards
    [bv_actual_aligned_dyadic_values_card_uniform_ws01b
      X hBV hFinite grid (T : ℝ) hAlign hGridMono hMesh]
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
    AV_Wave4_04A_AllTime.nested_finsets_common A hmono K hcard
  let Y : ℝ≥0 → ℝ := fun u => (u : ℝ) * X.drift - X.X u ω
  have hright : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u := by
    intro u
    have hc : Continuous (fun v : ℝ≥0 => (v : ℝ) * X.drift) :=
      NNReal.continuous_coe.mul continuous_const
    exact hc.continuousWithinAt.sub (X.rightCont ω u)
  have hclosed : IsClosed ((A N : Finset ℝ) : Set ℝ) :=
    (Finset.finite_toSet (A N)).isClosed
  refine ⟨A N, ?_⟩
  intro t ht
  obtain ⟨index, hindex, hge, htends⟩ := hRightCover t ht
  have hIn : ∀ n : ℕ, Y (grid n (index n)) ∈ A N := by
    intro n
    apply hN n
    change (grid n (index n) : ℝ) * X.drift -
      X.X (grid n (index n)) ω ∈
      (Finset.range (2 ^ n + 1)).image
        (fun i => (grid n i : ℝ) * X.drift - X.X (grid n i) ω)
    have hi : index n ≤ 2 ^ n := hindex n
    exact Finset.mem_image.mpr
      ⟨index n, Finset.mem_range.mpr (by omega), rfl⟩
  have htendsWithin :
      Tendsto (fun n => grid n (index n)) atTop (nhdsWithin t (Ici t)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨htends, Filter.Eventually.of_forall (fun n => hge n)⟩
  have hYtends :
      Tendsto (fun n => Y (grid n (index n))) atTop (nhds (Y t)) :=
    (hright t).tendsto.comp htendsWithin
  exact hclosed.mem_of_tendsto hYtends
    (Filter.Eventually.of_forall hIn)
