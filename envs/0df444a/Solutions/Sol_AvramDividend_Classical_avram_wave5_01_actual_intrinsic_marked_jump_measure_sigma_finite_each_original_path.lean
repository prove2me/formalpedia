-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_intrinsic_marked_jump_measure_sigma_finite_each_original_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:03:43.787551+00:00
-- url     : https://prove2.me/submissions/e8779712-c5c9-4df1-83c2-739946d6f655

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_countable_borel_support
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_single_time_atom_exact

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    SigmaFinite
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by
  classical
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  obtain ⟨S, hCount, hMeas, hZero⟩ :=
    avram_wave5_01_actual_source_marked_jump_measure_countable_borel_support X ω
  have hAtom (p : ℝ≥0 × ℝ) : μ {p} < ∞ := by
    have hEq : ({p.1} ×ˢ {p.2}) = ({p} : Set (ℝ≥0 × ℝ)) := by
      ext q
      simp [Prod.ext_iff]
    have hSource :=
      avram_wave5_01_actual_source_jump_measure_single_time_atom_exact
        X ω p.1 {p.2} (measurableSet_singleton p.2)
    change μ ({p.1} ×ˢ {p.2}) =
      ({u : ℝ≥0 | u = p.1 ∧ 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ ({p.2} : Set ℝ)}).encard
      at hSource
    have hSub :
        {u : ℝ≥0 | u = p.1 ∧ 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ ({p.2} : Set ℝ)}
          ⊆ ({p.1} : Set ℝ≥0) := by
      intro u hu
      exact hu.1
    have hCard := Set.encard_le_encard hSub
    have hFin : ({p.1} : Set ℝ≥0).encard < (∞ : ℝ≥0∞) := by simp
    rw [←hEq, hSource]
    exact lt_of_le_of_lt (by exact_mod_cast hCard) hFin
  let C : Set (Set (ℝ≥0 × ℝ)) :=
    insert Sᶜ ((fun p : ℝ≥0 × ℝ => ({p} : Set (ℝ≥0 × ℝ))) '' S)
  have hCcount : C.Countable := by
    exact (hCount.image fun p => ({p} : Set (ℝ≥0 × ℝ))).insert Sᶜ
  have hCMass : ∀ A ∈ C, μ A < ∞ := by
    intro A hA
    change A ∈ insert Sᶜ ((fun p : ℝ≥0 × ℝ => {p}) '' S) at hA
    rcases Set.mem_insert_iff.mp hA with hA | hA
    · subst A
      rw [hZero]
      exact ENNReal.zero_lt_top
    · rcases hA with ⟨p, hp, rfl⟩
      exact hAtom p
  have hCcover : ⋃₀ C = (Set.univ : Set (ℝ≥0 × ℝ)) := by
    ext p
    simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
    by_cases hp : p ∈ S
    · refine ⟨{p}, ?_, by simp⟩
      change {p} ∈ insert Sᶜ ((fun q : ℝ≥0 × ℝ => {q}) '' S)
      apply Set.mem_insert_iff.mpr
      exact Or.inr ⟨p, hp, rfl⟩
    · refine ⟨Sᶜ, ?_, hp⟩
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
  change SigmaFinite μ
  exact Measure.sigmaFinite_of_countable hCcount hCMass hCcover
