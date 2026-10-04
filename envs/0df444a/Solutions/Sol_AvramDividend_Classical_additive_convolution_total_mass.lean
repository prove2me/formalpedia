-- Prove2me | solution 1 for AvramDividend.Classical.additive_convolution_total_mass
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:11:49.742953+00:00
-- url     : https://prove2.me/submissions/7121998a-c028-4e80-94fa-182d59fde206

import Mathlib

set_option autoImplicit false

namespace Cex7b928beb

open MeasureTheory Set Cardinal

/-- There is a subset of `ℝ` that is not Borel measurable (cardinality argument). -/
theorem exists_not_measurableSet_real : ∃ N : Set ℝ, ¬ MeasurableSet N := by
  by_contra h
  push Not at h
  set S : Set (Set ℝ) := ⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) (b : ℝ)} with hS
  have hSc : #S ≤ 𝔠 := by
    have hcount : S.Countable := by
      refine Set.countable_iUnion fun a => Set.countable_iUnion fun b =>
        Set.countable_iUnion fun _ => Set.countable_singleton _
    exact (Cardinal.mk_le_aleph0_iff.mpr hcount.to_subtype).trans Cardinal.aleph0_le_continuum
  have hle := MeasurableSpace.cardinal_measurableSet_le_continuum hSc
  have heq : {t : Set ℝ | @MeasurableSet ℝ (MeasurableSpace.generateFrom S) t} = Set.univ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have : MeasurableSet t := h t
    rw [BorelSpace.measurable_eq (α := ℝ), Real.borel_eq_generateFrom_Ioo_rat] at this
    exact this
  rw [heq, Cardinal.mk_univ, Cardinal.mk_set, Cardinal.mk_real] at hle
  exact absurd hle (not_le.mpr (Cardinal.cantor 𝔠))

theorem cex : ¬ (∀ (μ ν : Measure ℝ),
    (Measure.conv μ ν) Set.univ = μ Set.univ * ν Set.univ) := by
  intro H
  obtain ⟨N, hN⟩ := exists_not_measurableSet_real
  have hNne : N.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hN MeasurableSet.empty
  set ν : Measure ℝ := Measure.count.restrict N with hν
  set κ : ℝ → Measure (ℝ × ℝ) := fun x => Measure.map (Prod.mk x) ν with hκ
  -- value of κ on the diagonal
  have hdiag : ∀ x, κ x (Set.diagonal ℝ) = N.indicator 1 x := by
    intro x
    simp only [hκ]
    rw [Measure.map_apply measurable_prodMk_left measurableSet_diagonal]
    have : (Prod.mk x ⁻¹' (Set.diagonal ℝ)) = {x} := by
      ext y; simp [Set.mem_diagonal_iff, eq_comm]
    rw [this, hν, Measure.restrict_apply (measurableSet_singleton x)]
    by_cases hx : x ∈ N
    · rw [show ({x} : Set ℝ) ∩ N = {x} from Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hx),
        Measure.count_singleton]
      simp [hx]
    · rw [Set.singleton_inter_eq_empty.mpr hx, measure_empty]
      simp [hx]
  have hnot : ¬ AEMeasurable κ Measure.count := by
    rintro ⟨g, hg, hκg⟩
    have hall : ∀ x, κ x = g x := by
      intro x
      by_contra hx
      have h0 : Measure.count {y | ¬ κ y = g y} = 0 := ae_iff.mp hκg
      rw [Measure.count_eq_zero_iff] at h0
      have : x ∈ {y | ¬ κ y = g y} := hx
      rw [h0] at this
      exact this
    have hmeasκ : Measurable κ := by
      have : κ = g := funext hall
      rw [this]; exact hg
    have hm : Measurable fun x => κ x (Set.diagonal ℝ) :=
      (Measure.measurable_coe measurableSet_diagonal).comp hmeasκ
    have hpre : MeasurableSet ((fun x => κ x (Set.diagonal ℝ)) ⁻¹' {1}) :=
      hm (measurableSet_singleton 1)
    have : (fun x => κ x (Set.diagonal ℝ)) ⁻¹' {1} = N := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hdiag]
      by_cases hx : x ∈ N <;> simp [hx]
    rw [this] at hpre
    exact hN hpre
  have hprod : (Measure.count : Measure ℝ).prod ν = 0 := by
    rw [Measure.prod_def, Measure.bind]
    change (Measure.map κ Measure.count).join = 0
    rw [Measure.map_of_not_aemeasurable hnot, Measure.join_zero]
  have hL : (Measure.conv (Measure.count : Measure ℝ) ν) Set.univ = 0 := by
    rw [Measure.conv, hprod, Measure.map_zero]
    rfl
  have hR : (Measure.count : Measure ℝ) Set.univ * ν Set.univ = ⊤ := by
    rw [Measure.count_apply_infinite Set.infinite_univ]
    apply ENNReal.top_mul
    rw [hν, Measure.restrict_apply_univ]
    exact (Measure.count_ne_zero hNne)
  have := H Measure.count ν
  rw [hL, hR] at this
  exact ENNReal.zero_ne_top this

end Cex7b928beb

open MeasureTheory Set in
theorem solution : ¬ (∀ (μ ν : Measure ℝ),
    (Measure.conv μ ν) Set.univ = μ Set.univ * ν Set.univ) := by
  exact Cex7b928beb.cex
