-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_true_fullcell_raw_centered_square_diff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:18:08.261108+00:00
-- url     : https://prove2.me/submissions/e508a286-0fcb-482d-8bab-1548f949b10f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem AvramDividend.Classical.avram_ga_original_true_fullcell_raw_centered_square_diff_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    ∀ m i : ℕ, Measurable (fun ω : Ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let R : ℝ := X.X (s + Δ) ω - X.X s ω
      let Z : ℝ := R - (Δ : ℝ) * X.c
      if s < ρ ω ∧ s + Δ ≤ ρ ω then R ^ 2 - Z ^ 2 else 0)
    := by
  intro m i
  have hX : ∀ t, Measurable (X.X t) := fun t => (X.adapted t).mono (𝓕.le t) le_rfl
  dsimp only
  set Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1) with hΔ
  set s : ℝ≥0 := (i : ℝ≥0) * Δ with hs
  have h1 : MeasurableSet {ω | s < ρ ω} := by
    have hm := hρstop.measurableSet_le s
    have h' : {ω | s < ρ ω} = {ω | (ρ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      rw [WithTop.coe_le_coe, not_le]
    rw [h']
    exact (𝓕.rightCont.le s _ hm).compl
  have h2 : MeasurableSet {ω | s + Δ ≤ ρ ω} := by
    have hm := hρstop.measurableSet_ge (s + Δ)
    have h' : {ω | s + Δ ≤ ρ ω} =
        {ω | ((s + Δ : ℝ≥0) : WithTop ℝ≥0) ≤ (ρ ω : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      exact WithTop.coe_le_coe.symm
    rw [h']
    exact 𝓕.rightCont.le _ _ hm
  have hset : MeasurableSet {ω | s < ρ ω ∧ s + Δ ≤ ρ ω} := h1.inter h2
  refine Measurable.ite hset ?_ measurable_const
  have hR : Measurable (fun ω => X.X (s + Δ) ω - X.X s ω) := (hX _).sub (hX _)
  exact (hR.pow_const 2).sub ((hR.sub measurable_const).pow_const 2)

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    ∀ m i : ℕ, Measurable (fun ω : Ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let R : ℝ := X.X (s + Δ) ω - X.X s ω
      let Z : ℝ := R - (Δ : ℝ) * X.c
      if s < ρ ω ∧ s + Δ ≤ ρ ω then R ^ 2 - Z ^ 2 else 0) :=
  AvramDividend.Classical.avram_ga_original_true_fullcell_raw_centered_square_diff_measurable X n ρ hρstop
