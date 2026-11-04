-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_grid_occupied_card_of_unique_source_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:21:01.483188+00:00
-- url     : https://prove2.me/submissions/4ba0c2ca-b3c1-4f8b-93be-e7714875030a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

/-- A uniquely covered finite source marked-jump set occupies exactly its own number of grid cells. -/
private theorem w706_finite_occupied_card_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (I : Finset β) (R : α → β → Prop)
    (hCover : ∀ a ∈ F, ∃ b ∈ I, R a b)
    (hSingle : ∀ b ∈ I, ∀ a ∈ F, ∀ a' ∈ F,
      R a b → R a' b → a = a')
    (hIndexUnique : ∀ a ∈ F, ∀ b ∈ I, ∀ b' ∈ I,
      R a b → R a b' → b = b') :
    (I.filter (fun b => ∃ a ∈ F, R a b)).card = F.card := by
  classical
  let A : Finset β := I.filter (fun b => ∃ a ∈ F, R a b)
  have hWitness (b : β) (hb : b ∈ A) : ∃ a ∈ F, R a b :=
    (Finset.mem_filter.mp hb).2
  let f (b : β) (hb : b ∈ A) : α := Classical.choose (hWitness b hb)
  have hf (b : β) (hb : b ∈ A) :
      f b hb ∈ F ∧ R (f b hb) b := Classical.choose_spec (hWitness b hb)
  change A.card = F.card
  refine Finset.card_bij f ?_ ?_ ?_
  · intro b hb
    exact (hf b hb).1
  · intro b hb c hc heq
    have hcRel : R (f b hb) c := by
      simpa only [heq] using (hf c hc).2
    exact hIndexUnique (f b hb) (hf b hb).1 b
      (Finset.mem_filter.mp hb).1 c (Finset.mem_filter.mp hc).1
      (hf b hb).2 hcRel
  · intro a ha
    obtain ⟨b, hb, hab⟩ := hCover a ha
    have hbA : b ∈ A :=
      Finset.mem_filter.mpr ⟨hb, ⟨a, ha, hab⟩⟩
    refine ⟨b, hbA, ?_⟩
    exact hSingle b hb (f b hbA) (hf b hbA).1
      a ha (hf b hbA).2 hab

/-- Exact original negative-band intrinsic count equals uniquely occupied source grid cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (k m : ℕ) (grid : ℕ → ℝ≥0)
    (S : Set ℝ≥0)
    (hS : S = {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -(1 / ((k : ℝ) + 1))})
    (hCover : ∀ u : ℝ≥0, u ∈ S →
      ∃ i : ℕ, i < m ∧ u ∈ Ioc (grid i) (grid (i + 1)))
    (hSingle : ∀ i : ℕ, i < m → ∀ u v : ℝ≥0,
      u ∈ S → v ∈ S →
      u ∈ Ioc (grid i) (grid (i + 1)) →
      v ∈ Ioc (grid i) (grid (i + 1)) → u = v)
    (hIndexUnique : ∀ u : ℝ≥0, u ∈ S → ∀ i j : ℕ,
      i < m → j < m →
      u ∈ Ioc (grid i) (grid (i + 1)) →
      u ∈ Ioc (grid j) (grid (j + 1)) → i = j) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1)))) =
    (((Finset.range m).filter (fun i =>
      ∃ u : ℝ≥0, u ∈ S ∧ u ∈ Ioc (grid i) (grid (i + 1)))).card :
        ℝ≥0∞) := by
  classical
  have hFin : S.Finite := by
    rw [hS]
    exact avram_wave7_06_original_negative_band_marked_times_finite X ω T k
  let F : Finset ℝ≥0 := hFin.toFinset
  have hF (u : ℝ≥0) : u ∈ F ↔ u ∈ S :=
    Set.Finite.mem_toFinset hFin
  have hC : ∀ u ∈ F, ∃ i ∈ Finset.range m,
      u ∈ Ioc (grid i) (grid (i + 1)) := by
    intro u hu
    obtain ⟨i, hi, hcell⟩ := hCover u ((hF u).mp hu)
    exact ⟨i, Finset.mem_range.mpr hi, hcell⟩
  have hOne : ∀ i ∈ Finset.range m, ∀ u ∈ F, ∀ v ∈ F,
      u ∈ Ioc (grid i) (grid (i + 1)) →
      v ∈ Ioc (grid i) (grid (i + 1)) → u = v := by
    intro i hi u hu v hv huCell hvCell
    exact hSingle i (Finset.mem_range.mp hi) u v
      ((hF u).mp hu) ((hF v).mp hv) huCell hvCell
  have hIdx : ∀ u ∈ F, ∀ i ∈ Finset.range m,
      ∀ j ∈ Finset.range m,
      u ∈ Ioc (grid i) (grid (i + 1)) →
      u ∈ Ioc (grid j) (grid (j + 1)) → i = j := by
    intro u hu i hi j hj hiCell hjCell
    exact hIndexUnique u ((hF u).mp hu) i j
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      hiCell hjCell
  have hCard :
      ((Finset.range m).filter (fun i =>
        ∃ u : ℝ≥0, u ∈ S ∧
          u ∈ Ioc (grid i) (grid (i + 1)))).card = F.card := by
    have hBij := w706_finite_occupied_card_eq F (Finset.range m)
      (fun u i => u ∈ Ioc (grid i) (grid (i + 1))) hC hOne hIdx
    convert hBij using 1
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, u, hu, hcell⟩
      exact ⟨hi, u, (hF u).mpr hu, hcell⟩
    · rintro ⟨hi, u, hu, hcell⟩
      exact ⟨hi, u, (hF u).mp hu, hcell⟩
  have hCount :
      ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1)))) =
        (S.ncard : ℝ≥0∞) := by
    rw [hS]
    exact avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
      X ω T k
  calc
    _ = (S.ncard : ℝ≥0∞) := hCount
    _ = (F.card : ℝ≥0∞) := by
      exact congrArg (fun x : ℕ => (x : ℝ≥0∞))
        (Set.ncard_eq_toFinset_card S hFin)
    _ = (((Finset.range m).filter (fun i =>
          ∃ u : ℝ≥0, u ∈ S ∧
            u ∈ Ioc (grid i) (grid (i + 1)))).card : ℝ≥0∞) := by
      exact congrArg (fun x : ℕ => (x : ℝ≥0∞)) hCard.symm
