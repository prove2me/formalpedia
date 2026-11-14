-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_simple_family_disjoint_energy_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:17:19.417289+00:00
-- url     : https://prove2.me/submissions/5da1513a-bfe8-4021-9731-6e4a4f13a243

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_nat_stage_exact_energy_20261112
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- Simultaneous natural-indexed original marked jump fibre stages for
any sequence of unit bounded finite-range Borel marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hNeg : S ⊆ Iio (0 : ℝ))
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hBound : ∀ k z, z ∈ S → |f k z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∃ (K : ℕ → ℕ) (B : ℕ → ℕ → Set ℝ)
      (c : ℕ → ℕ → ℝ),
      let F : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (K k), c k i *
          ((NX ω (Ioc 0 T ×ˢ B k i)).toReal -
            (((T : ℝ≥0∞) * X.ν (B k i)).toReal))
      let E : ℕ → ℝ := fun k =>
        ∑ i ∈ Finset.range (K k), (c k i)^2 *
          (((T : ℝ≥0∞) * X.ν (B k i)).toReal)
      (∀ k, ∀ i ∈ Finset.range (K k),
        MeasurableSet (B k i) ∧ B k i ⊆ S) ∧
      (∀ k, ∀ i ∈ Finset.range (K k),
        ∀ j ∈ Finset.range (K k), i ≠ j →
          Disjoint (B k i) (B k j)) ∧
      (∀ k, ∀ᵐ ω ∂P, F k ω =
        (∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω) -
          (T : ℝ) * (∫ z in S, f k z ∂X.ν)) ∧
      (∀ k, Integrable (fun ω => (F k ω)^2) P) ∧
      (∀ k, (∫ ω, (F k ω)^2 ∂P) = E k) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hStages : ∀ k, ∃ (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ),
      (∀ i ∈ Finset.range K, MeasurableSet (B i) ∧ B i ⊆ S) ∧
      (∀ i ∈ Finset.range K, ∀ j ∈ Finset.range K,
        i ≠ j → Disjoint (B i) (B j)) ∧
      let F : Ω → ℝ := fun ω => ∑ i ∈ Finset.range K,
        c i * ((NX ω (Ioc 0 T ×ˢ B i)).toReal -
          (((T : ℝ≥0∞) * X.ν (B i)).toReal))
      let E : ℝ := ∑ i ∈ Finset.range K, (c i)^2 *
        (((T : ℝ≥0∞) * X.ν (B i)).toReal)
      (∀ᵐ ω ∂P, F ω =
        (∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω) -
          (T : ℝ) * (∫ z in S, f k z ∂X.ν)) ∧
      Integrable (fun ω => (F ω)^2) P ∧
      (∫ ω, (F ω)^2 ∂P) = E := by
    intro k
    exact avram_a21_original_simple_nat_stage_exact_energy_20261112
      X hFinite T S hS hNeg (f k) (fun z hz => hBound k z hz)
  choose K B c hData using hStages
  refine ⟨K, B, c, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; exact (hData k).1
  · intro k; exact (hData k).2.1
  · intro k; exact (hData k).2.2.1
  · intro k; exact (hData k).2.2.2.1
  · intro k; exact (hData k).2.2.2.2
