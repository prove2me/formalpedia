-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_jump_count_eq_finite_grid_occupancy_of_unique_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:06:21.649206+00:00
-- url     : https://prove2.me/submissions/5bf93134-5f11-43bd-a2de-b551411d171e


import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
private theorem finite_occupied_card_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (I : Finset β) (R : α → β → Prop)
    [DecidablePred (fun b : β => ∃ a ∈ F, R a b)]
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
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ) (grid : ℕ → ℝ≥0)
    (S : Set ℝ≥0)
    (hS : S = {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0})
    (hFin : S.Finite)
    (hCover : ∀ u : ℝ≥0, u ∈ S →
      ∃ i : ℕ, i < n ∧ u ∈ Ioc (grid i) (grid (i + 1)))
    (hSingle : ∀ i : ℕ, i < n → ∀ u v : ℝ≥0,
      u ∈ S → v ∈ S →
      u ∈ Ioc (grid i) (grid (i + 1)) →
      v ∈ Ioc (grid i) (grid (i + 1)) → u = v)
    (hIndexUnique : ∀ u : ℝ≥0, u ∈ S → ∀ i j : ℕ,
      i < n → j < n →
      u ∈ Ioc (grid i) (grid (i + 1)) →
      u ∈ Ioc (grid j) (grid (j + 1)) → i = j) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) =
    ({i : ℕ | i < n ∧ ∃ u : ℝ≥0,
      u ∈ S ∧ u ∈ Ioc (grid i) (grid (i + 1))}.ncard : ENNReal) := by
  classical
  let F : Finset ℝ≥0 := hFin.toFinset
  have hF (u : ℝ≥0) : u ∈ F ↔ u ∈ S := by
    exact Set.Finite.mem_toFinset hFin
  have hC : ∀ u ∈ F, ∃ i ∈ Finset.range n,
      u ∈ Ioc (grid i) (grid (i + 1)) := by
    intro u hu
    obtain ⟨i, hi, hcell⟩ := hCover u ((hF u).mp hu)
    exact ⟨i, Finset.mem_range.mpr hi, hcell⟩
  have hOne : ∀ i ∈ Finset.range n, ∀ u ∈ F, ∀ v ∈ F,
      u ∈ Ioc (grid i) (grid (i + 1)) →
      v ∈ Ioc (grid i) (grid (i + 1)) → u = v := by
    intro i hi u hu v hv huCell hvCell
    exact hSingle i (Finset.mem_range.mp hi) u v
      ((hF u).mp hu) ((hF v).mp hv) huCell hvCell
  have hIdx : ∀ u ∈ F, ∀ i ∈ Finset.range n,
      ∀ j ∈ Finset.range n,
      u ∈ Ioc (grid i) (grid (i + 1)) →
      u ∈ Ioc (grid j) (grid (j + 1)) → i = j := by
    intro u hu i hi j hj hiCell hjCell
    exact hIndexUnique u ((hF u).mp hu) i j
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      hiCell hjCell
  have hCard :
      ((Finset.range n).filter (fun i =>
        ∃ u : ℝ≥0, u ∈ S ∧
          u ∈ Ioc (grid i) (grid (i + 1)))).card = F.card := by
    have hBij := finite_occupied_card_eq F (Finset.range n)
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
  have hRect :=
    avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
      X ω 0 T (Set.univ : Set ℝ) MeasurableSet.univ
  have hSet :
      {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈
          (Set.univ : Set ℝ)} = S := by
    rw [hS]
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_univ, and_true]
    tauto
  have hCount :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) = S.encard := by
    rw [hSet] at hRect; exact hRect
  let A : Set ℕ := {i : ℕ | i < n ∧ ∃ u : ℝ≥0,
    u ∈ S ∧ u ∈ Ioc (grid i) (grid (i + 1))}
  have hAFinite : A.Finite := by
    apply (Set.finite_lt_nat n).subset
    intro i hi; exact hi.1
  have hACard :
      A.ncard =
        ((Finset.range n).filter (fun i =>
          ∃ u : ℝ≥0, u ∈ S ∧
            u ∈ Ioc (grid i) (grid (i + 1)))).card := by
    rw [Set.ncard_eq_toFinset_card A hAFinite]
    congr 1
    ext i
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter,
      Finset.mem_range, A, Set.mem_setOf_eq]
  change _ = (A.ncard : ENNReal)
  calc
    _ = (S.encard : ENNReal) := hCount
    _ = (F.card : ENNReal) := by
      exact_mod_cast hFin.encard_eq_coe_toFinset_card
    _ = (A.ncard : ENNReal) := by
      exact congrArg (fun k : ℕ => (k : ENNReal))
        (hCard.symm.trans hACard.symm)