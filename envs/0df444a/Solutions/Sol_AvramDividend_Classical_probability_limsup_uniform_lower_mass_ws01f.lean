-- Prove2me | solution 1 for AvramDividend.Classical.probability_limsup_uniform_lower_mass_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:07:50.325115+00:00
-- url     : https://prove2.me/submissions/b7334970-9e09-4d2a-87fe-a27795a1b586

import Mathlib
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (p : ℝ) (hp : 0 < p)
    (N : ℕ) (hmass : ∀ n ≥ N, p ≤ μ.real (A n)) :
    p ≤ μ.real (⋂ k : ℕ, ⋃ n : ℕ,
      {ω : Ω | k ≤ n ∧ ω ∈ A n}) := by
  let T : ℕ → Set Ω := fun k =>
    ⋃ n : ℕ, {ω : Ω | k ≤ n ∧ ω ∈ A n}
  have hT (k : ℕ) : MeasurableSet (T k) := by
    dsimp [T]
    apply MeasurableSet.iUnion
    intro n
    by_cases hkn : k ≤ n
    · simpa [hkn] using hA n
    · simpa [hkn] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  have hanti : Antitone T := by
    intro k l hkl ω hω
    change ω ∈ ⋃ n : ℕ, {z : Ω | l ≤ n ∧ z ∈ A n} at hω
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
    change ω ∈ ⋃ n : ℕ, {z : Ω | k ≤ n ∧ z ∈ A n}
    exact Set.mem_iUnion.mpr ⟨n, le_trans hkl hn.1, hn.2⟩
  have hInter :
      μ (⋂ k : ℕ, T k) = ⨅ k : ℕ, μ (T k) :=
    hanti.measure_iInter
      (fun k => (hT k).nullMeasurableSet)
      ⟨0, measure_ne_top μ (T 0)⟩
  have htail (k : ℕ) : ENNReal.ofReal p ≤ μ (T k) := by
    let n : ℕ := max k N
    have hkn : k ≤ n := le_max_left _ _
    have hNn : N ≤ n := le_max_right _ _
    have hsub : A n ⊆ T k := by
      intro ω hω
      change ω ∈ ⋃ j : ℕ, {z : Ω | k ≤ j ∧ z ∈ A j}
      exact Set.mem_iUnion.mpr ⟨n, hkn, hω⟩
    have hreal : ENNReal.ofReal p ≤ μ (A n) :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ (A n))).mpr
        (hmass n hNn)
    exact le_trans hreal (measure_mono hsub)
  have hmassInter : ENNReal.ofReal p ≤ μ (⋂ k : ℕ, T k) := by
    rw [hInter]
    exact le_iInf htail
  have hrealInter : p ≤ μ.real (⋂ k : ℕ, T k) :=
    (ENNReal.ofReal_le_iff_le_toReal
      (measure_ne_top μ (⋂ k : ℕ, T k))).mp hmassInter
  simpa only [T] using hrealInter
