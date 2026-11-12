-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_generic_joint_law_of_strict_positive_right_ray_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:02:39.542204+00:00
-- url     : https://prove2.me/submissions/0d64b0bf-6157-466a-a7ec-afe8b6c9c3e1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem avram_a06_local_positive_ray_ext
    (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    (hMass : μ Set.univ = ν Set.univ)
    (hSupport : μ (Set.Ioi 0) = μ Set.univ)
    (hRay : ∀ t : ℝ, 0 ≤ t →
      μ (Set.Ioi t) = ν (Set.Ioi t)) :
    μ = ν := by
  have hνSupport : ν (Ioi (0 : ℝ)) = ν univ := by
    calc
      ν (Ioi (0 : ℝ)) = μ (Ioi 0) := (hRay 0 le_rfl).symm
      _ = μ univ := hSupport
      _ = ν univ := hMass
  have hAll (t : ℝ) : μ (Ioi t) = ν (Ioi t) := by
    by_cases ht : 0 ≤ t
    · exact hRay t ht
    · have hlt : t < 0 := lt_of_not_ge ht
      have hsub : Ioi (0 : ℝ) ⊆ Ioi t := by
        intro x hx
        exact lt_trans hlt hx
      have hμ : μ (Ioi t) = μ univ := by
        apply le_antisymm (measure_mono (subset_univ _))
        calc
          μ univ = μ (Ioi 0) := hSupport.symm
          _ ≤ μ (Ioi t) := measure_mono hsub
      have hν : ν (Ioi t) = ν univ := by
        apply le_antisymm (measure_mono (subset_univ _))
        calc
          ν univ = ν (Ioi 0) := hνSupport.symm
          _ ≤ ν (Ioi t) := measure_mono hsub
      exact hμ.trans (hMass.trans hν.symm)
  haveI : IsFiniteMeasure ν := ⟨by simp [← hMass]⟩
  apply Measure.ext_of_Iic μ ν
  intro a
  calc
    μ (Iic a) = μ univ - μ (Ioi a) := by
      simpa only [Set.compl_Ioi] using
        (measure_compl (measurableSet_Ioi) (measure_ne_top μ (Ioi a)))
    _ = ν univ - ν (Ioi a) := by rw [hMass, hAll]
    _ = ν (Iic a) := by
      simpa only [Set.compl_Ioi] using
        (measure_compl (measurableSet_Ioi) (measure_ne_top ν (Ioi a))).symm


/-- Rectangular right-tail probabilities determine the joint law when the
    real coordinate is strictly positive almost surely. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R U : Ω → ℝ) (F G : Ω → (ℕ → ℝ))
    (hRF : AEMeasurable (fun ω => (R ω, F ω)) P)
    (hUG : AEMeasurable (fun ω => (U ω, G ω)) P)
    (hRpos : ∀ᵐ ω ∂P, 0 < R ω)
    (hUpos : ∀ᵐ ω ∂P, 0 < U ω)
    (hrect : ∀ (t : ℝ), 0 ≤ t →
      ∀ (B : Set (ℕ → ℝ)), MeasurableSet B →
      P {ω | t < R ω ∧ F ω ∈ B} =
      P {ω | t < U ω ∧ G ω ∈ B}) :
    IdentDistrib (fun ω => (R ω, F ω)) (fun ω => (U ω, G ω)) P P := by
  let μ : Measure (ℝ × (ℕ → ℝ)) := P.map (fun ω => (R ω, F ω))
  let ν : Measure (ℝ × (ℕ → ℝ)) := P.map (fun ω => (U ω, G ω))
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, Measure.map_apply_of_aemeasurable hRF]⟩
  have hjoint : μ = ν := by
    apply Measure.ext_prod
    intro S B hS hB
    let μB : Measure ℝ := (μ.restrict (univ ×ˢ B)).map Prod.fst
    let νB : Measure ℝ := (ν.restrict (univ ×ˢ B)).map Prod.fst
    have hμBrect (T : Set ℝ) (hT : MeasurableSet T) :
        μB T = μ (T ×ˢ B) := by
      rw [show μB T = (μ.restrict (univ ×ˢ B)) (Prod.fst ⁻¹' T) from
        Measure.map_apply measurable_fst hT]
      rw [Measure.restrict_apply' (MeasurableSet.univ.prod hB)]
      congr 1
      ext z
      simp [Set.mem_prod]
    have hνBrect (T : Set ℝ) (hT : MeasurableSet T) :
        νB T = ν (T ×ˢ B) := by
      rw [show νB T = (ν.restrict (univ ×ˢ B)) (Prod.fst ⁻¹' T) from
        Measure.map_apply measurable_fst hT]
      rw [Measure.restrict_apply' (MeasurableSet.univ.prod hB)]
      congr 1
      ext z
      simp [Set.mem_prod]
    have hμB (T : Set ℝ) (hT : MeasurableSet T) :
        μB T = P {ω | R ω ∈ T ∧ F ω ∈ B} := by
      rw [hμBrect T hT]
      change (P.map (fun ω => (R ω, F ω))) (T ×ˢ B) = _
      rw [Measure.map_apply_of_aemeasurable hRF (hT.prod hB)]
      congr 1
    have hνB (T : Set ℝ) (hT : MeasurableSet T) :
        νB T = P {ω | U ω ∈ T ∧ G ω ∈ B} := by
      rw [hνBrect T hT]
      change (P.map (fun ω => (U ω, G ω))) (T ×ˢ B) = _
      rw [Measure.map_apply_of_aemeasurable hUG (hT.prod hB)]
      congr 1
    haveI : IsFiniteMeasure μB := ⟨by
      rw [hμB univ MeasurableSet.univ]
      exact lt_of_le_of_lt (measure_mono (subset_univ _))
        (measure_lt_top P univ)⟩
    have hμPositive : μB (Ioi (0 : ℝ)) = μB univ := by
      rw [hμB (Ioi 0) measurableSet_Ioi, hμB univ MeasurableSet.univ]
      apply measure_congr
      filter_upwards [hRpos] with ω hp
      apply propext
      change (0 < R ω ∧ F ω ∈ B) ↔ (True ∧ F ω ∈ B)
      simp [hp]
    have hνPositive : νB (Ioi (0 : ℝ)) = νB univ := by
      rw [hνB (Ioi 0) measurableSet_Ioi, hνB univ MeasurableSet.univ]
      apply measure_congr
      filter_upwards [hUpos] with ω hp
      apply propext
      change (0 < U ω ∧ G ω ∈ B) ↔ (True ∧ G ω ∈ B)
      simp [hp]
    have hBMass : μB univ = νB univ := by
      calc
        μB univ = μB (Ioi 0) := hμPositive.symm
        _ = P {ω | 0 < R ω ∧ F ω ∈ B} :=
          hμB (Ioi 0) measurableSet_Ioi
        _ = P {ω | 0 < U ω ∧ G ω ∈ B} :=
          hrect 0 le_rfl B hB
        _ = νB (Ioi 0) := (hνB (Ioi 0) measurableSet_Ioi).symm
        _ = νB univ := hνPositive
    have hBRay (t : ℝ) (ht : 0 ≤ t) :
        μB (Ioi t) = νB (Ioi t) := by
      rw [hμB (Ioi t) measurableSet_Ioi,
          hνB (Ioi t) measurableSet_Ioi]
      exact hrect t ht B hB
    have hBEqual :=
      avram_a06_local_positive_ray_ext
        μB νB hBMass hμPositive hBRay
    calc
      μ (S ×ˢ B) = μB S := (hμBrect S hS).symm
      _ = νB S := by rw [hBEqual]
      _ = ν (S ×ˢ B) := hνBrect S hS
  exact ⟨hRF, hUG, hjoint⟩
