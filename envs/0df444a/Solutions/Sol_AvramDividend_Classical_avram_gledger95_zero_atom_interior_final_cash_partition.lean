-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger95_zero_atom_interior_final_cash_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:48:30.226277+00:00
-- url     : https://prove2.me/submissions/a424c007-f298-4e1d-bbcf-ffe92998b6fd

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger90_masked_monotone_grid_Ioc_cash_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hSnonneg : ∀ s ∈ S, 0 ≤ s)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (ρ : ℝ) (hvk : v k < ρ)
    (hstop : v (k + 1) = ρ) :
    (∫⁻ s in S ∩ Iio ρ, f s ∂μ) =
      (∫⁻ s in S ∩ {0}, f s ∂μ) +
      (∑ i ∈ Finset.range k,
        ∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ) +
      (∫⁻ s in S ∩ Ioo (v k) ρ, f s ∂μ) := by
  have hvk0 : 0 ≤ v k := by
    rw [← hv0]
    exact hv (Nat.zero_le k)
  have hρ0 : 0 < ρ := lt_of_le_of_lt hvk0 hvk
  have hset : S ∩ Iio ρ =
      (S ∩ {0}) ∪
        ((S ∩ Ioc (v 0) (v k)) ∪ (S ∩ Ioo (v k) ρ)) := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_union, mem_singleton_iff, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨htS, htρ⟩
      by_cases hzero : t = 0
      · exact Or.inl ⟨htS, hzero⟩
      · have ht0 : 0 < t := lt_of_le_of_ne (hSnonneg t htS) (Ne.symm hzero)
        right
        by_cases htk : t ≤ v k
        · exact Or.inl ⟨htS, by simpa [hv0] using ht0, htk⟩
        · exact Or.inr ⟨htS, lt_of_not_ge htk, htρ⟩
    · rintro (hzero | hinter | hfinal)
      · rcases hzero with ⟨htS, rfl⟩
        exact ⟨htS, hρ0⟩
      · exact ⟨hinter.1, lt_of_le_of_lt hinter.2.2 hvk⟩
      · exact ⟨hfinal.1, hfinal.2.2⟩
  have hdA : Disjoint (S ∩ {0})
      ((S ∩ Ioc (v 0) (v k)) ∪ (S ∩ Ioo (v k) ρ)) := by
    apply Set.disjoint_left.mpr
    intro t htA htBC
    have ht0 : t = 0 := htA.2
    subst t
    rcases htBC with htB | htC
    · have hbad := htB.2.1
      rw [hv0] at hbad
      exact (lt_irrefl (0 : ℝ)) hbad
    · exact (not_lt_of_ge hvk0) htC.2.1
  have hdBC : Disjoint (S ∩ Ioc (v 0) (v k))
      (S ∩ Ioo (v k) ρ) := by
    apply Set.disjoint_left.mpr
    intro t htB htC
    exact (not_lt_of_ge htB.2.2) htC.2.1
  have hpart := avram_gledger90_masked_monotone_grid_Ioc_cash_partition μ f S hS v hv k
  have hUnion1 :
      (∫⁻ s in S ∩ Iio ρ, f s ∂μ) =
        (∫⁻ s in S ∩ {0}, f s ∂μ) +
        (∫⁻ s in (S ∩ Ioc (v 0) (v k)) ∪
          (S ∩ Ioo (v k) ρ), f s ∂μ) := by
    rw [hset]
    exact lintegral_union
      ((hS.inter measurableSet_Ioc).union
        (hS.inter measurableSet_Ioo)) hdA
  have hUnion2 :
      (∫⁻ s in (S ∩ Ioc (v 0) (v k)) ∪
        (S ∩ Ioo (v k) ρ), f s ∂μ) =
        (∫⁻ s in S ∩ Ioc (v 0) (v k), f s ∂μ) +
        (∫⁻ s in S ∩ Ioo (v k) ρ, f s ∂μ) :=
    lintegral_union (hS.inter measurableSet_Ioo) hdBC
  calc
    (∫⁻ s in S ∩ Iio ρ, f s ∂μ) =
        (∫⁻ s in S ∩ {0}, f s ∂μ) +
        (∫⁻ s in S ∩ Ioc (v 0) (v k), f s ∂μ) +
        (∫⁻ s in S ∩ Ioo (v k) ρ, f s ∂μ) := by
      rw [hUnion1, hUnion2]
      ac_rfl
    _ = _ := by rw [hpart]
