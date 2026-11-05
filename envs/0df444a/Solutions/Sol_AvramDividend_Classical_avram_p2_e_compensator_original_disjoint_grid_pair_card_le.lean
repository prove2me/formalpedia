-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_disjoint_grid_pair_card_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:36:53.809021+00:00
-- url     : https://prove2.me/submissions/dcd3d3fe-dc84-4d54-bc76-afa2be802ff5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Source chronological crossing-pair counts on disjoint time cells never exceed all pairs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (m : ℕ) (s t : Fin m → ℝ≥0) (n : ℕ)
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint (Ioc (s i) (t i)) (Ioc (s j) (t j))) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let C : Fin m → Finset (ℝ≥0 × ℝ≥0) := fun i =>
      (F ×ˢ F).filter (fun p => p.1 ≤ s i ∧ s i < p.2 ∧ p.2 ≤ t i)
    (∑ i, (C i).card) ≤
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by
  classical
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let C : Fin m → Finset (ℝ≥0 × ℝ≥0) := fun i =>
    (F ×ˢ F).filter (fun p => p.1 ≤ s i ∧ s i < p.2 ∧ p.2 ≤ t i)
  let K : Finset (ℝ≥0 × ℝ≥0) :=
    (F ×ˢ F).filter (fun p => p.1 < p.2)
  change (∑ i, (C i).card) ≤ K.card
  have hpair : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint C := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hi : s i < p.2 ∧ p.2 ≤ t i :=
      (Finset.mem_filter.mp hpi).2.2
    have hj : s j < p.2 ∧ p.2 ≤ t j :=
      (Finset.mem_filter.mp hpj).2.2
    exact (Set.disjoint_left.mp (hdisj i j hij)) hi hj
  have hsubset : (Finset.univ.biUnion C) ⊆ K := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨i, _, hpi⟩
    rcases Finset.mem_filter.mp hpi with ⟨hprod, hcross⟩
    exact Finset.mem_filter.mpr
      ⟨hprod, lt_of_le_of_lt hcross.1 hcross.2.1⟩
  calc
    (∑ i, (C i).card) = (Finset.univ.biUnion C).card :=
      (Finset.card_biUnion hpair).symm
    _ ≤ K.card := Finset.card_le_card hsubset
