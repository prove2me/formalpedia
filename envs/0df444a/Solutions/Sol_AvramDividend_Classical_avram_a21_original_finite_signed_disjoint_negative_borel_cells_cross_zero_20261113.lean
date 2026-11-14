-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_finite_signed_disjoint_negative_borel_cells_cross_zero_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:49:59.37013+00:00
-- url     : https://prove2.me/submissions/52a39cb8-ed54-4f5c-8211-b6b1a5d19f46

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_weighted_disjoint_negative_borel_counts_cross_zero_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Finite signed simple marked jump fields are orthogonal on disjoint mark supports. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι) (G : Finset κ)
    (A : ι → Set ℝ) (B : κ → Set ℝ)
    (a : ι → ℝ) (b : κ → ℝ)
    (hA : ∀ i ∈ F, MeasurableSet (A i))
    (hB : ∀ j ∈ G, MeasurableSet (B j))
    (hNegA : ∀ i ∈ F, A i ⊆ Iio (0 : ℝ))
    (hNegB : ∀ j ∈ G, B j ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ F, ∀ j ∈ G, Disjoint (A i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let YA : ι → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 T ×ˢ A i)).toReal -
        ((T : ℝ≥0∞) * X.ν (A i)).toReal
    let YB : κ → Ω → ℝ := fun j ω =>
      (NX ω (Ioc 0 T ×ˢ B j)).toReal -
        ((T : ℝ≥0∞) * X.ν (B j)).toReal
    Integrable (fun ω => (∑ i ∈ F, a i * YA i ω) *
      (∑ j ∈ G, b j * YB j ω)) P ∧
      (∫ ω, (∑ i ∈ F, a i * YA i ω) *
        (∑ j ∈ G, b j * YB j ω) ∂P) = 0 := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let YA : ι → Ω → ℝ := fun i ω =>
    (NX ω (Ioc 0 T ×ˢ A i)).toReal -
      ((T : ℝ≥0∞) * X.ν (A i)).toReal
  let YB : κ → Ω → ℝ := fun j ω =>
    (NX ω (Ioc 0 T ×ˢ B j)).toReal -
      ((T : ℝ≥0∞) * X.ν (B j)).toReal
  let W : ι → κ → Ω → ℝ :=
    fun i j ω => (a i * YA i ω) * (b j * YB j ω)
  have hPair (i : ι) (hi : i ∈ F) (j : κ) (hj : j ∈ G) :
      Integrable (W i j) P ∧ (∫ ω, W i j ω ∂P) = 0 := by
    have h := avram_a21_original_weighted_disjoint_negative_borel_counts_cross_zero_20261113
      X hFinite T (A i) (B j)
      (hA i hi) (hB j hj) (hNegA i hi) (hNegB j hj)
      (hDisj i hi j hj) (a i) (b j)
    change Integrable (W i j) P ∧ (∫ ω, W i j ω ∂P) = 0 at h
    exact h
  have hInner (i : ι) (hi : i ∈ F) :
      Integrable (fun ω => ∑ j ∈ G, W i j ω) P :=
    integrable_finsetSum G (fun j hj => (hPair i hi j hj).1)
  have hAll :
      Integrable (fun ω => ∑ i ∈ F, ∑ j ∈ G, W i j ω) P :=
    integrable_finsetSum F hInner
  have hExpand :
      (fun ω => (∑ i ∈ F, a i * YA i ω) *
        (∑ j ∈ G, b j * YB j ω)) =
      (fun ω => ∑ i ∈ F, ∑ j ∈ G, W i j ω) := by
    funext ω
    dsimp [W]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hEachZero (i : ι) (hi : i ∈ F) :
      (∫ ω, ∑ j ∈ G, W i j ω ∂P) = 0 := by
    rw [integral_finsetSum G (fun j hj => (hPair i hi j hj).1)]
    apply Finset.sum_eq_zero
    intro j hj
    exact (hPair i hi j hj).2
  have hSumZero :
      (∫ ω, ∑ i ∈ F, ∑ j ∈ G, W i j ω ∂P) = 0 := by
    rw [integral_finsetSum F hInner]
    apply Finset.sum_eq_zero
    intro i hi
    exact hEachZero i hi
  change Integrable (fun ω => (∑ i ∈ F, a i * YA i ω) *
    (∑ j ∈ G, b j * YB j ω)) P ∧
    (∫ ω, (∑ i ∈ F, a i * YA i ω) *
      (∑ j ∈ G, b j * YB j ω) ∂P) = 0
  rw [hExpand]
  exact ⟨hAll, hSumZero⟩
