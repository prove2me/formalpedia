-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_cdf_cylinders_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:30:30.619405+00:00
-- url     : https://prove2.me/submissions/91a70918-b6d8-49df-94d6-67f37555c1fa

import Mathlib
open MeasureTheory Set ProbabilityTheory

theorem solution
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hR : Measurable R)
    (Y : Ω → β) (hY : Measurable Y)
    (hCDF : ∀ (a : ℝ) (B : Set β), MeasurableSet B →
      P (R ⁻¹' (Iic a) ∩ Y ⁻¹' B) =
        P (R ⁻¹' (Iic a)) * P (Y ⁻¹' B)) :
    IndepFun R Y P := by
  rw [IndepFun_iff_Indep]
  let p1 : Set (Set Ω) := (fun s => R ⁻¹' s) '' (range Iic)
  let p2 : Set (Set Ω) := {s | MeasurableSet[MeasurableSpace.comap Y inferInstance] s}
  refine IndepSets.indep (p1 := p1) (p2 := p2) hR.comap_le hY.comap_le ?_ ?_ ?_ ?_ ?_
  · exact isPiSystem_Iic.comap R
  · exact @MeasurableSpace.isPiSystem_measurableSet Ω (MeasurableSpace.comap Y inferInstance)
  · have hb : Real.measurableSpace = MeasurableSpace.generateFrom (range Iic) := by
      rw [← borel_eq_generateFrom_Iic ℝ]; exact (BorelSpace.measurable_eq (α := ℝ))
    rw [hb, MeasurableSpace.comap_generateFrom]
  · exact (@MeasurableSpace.generateFrom_measurableSet Ω (MeasurableSpace.comap Y inferInstance)).symm
  · rw [IndepSets_iff]
    rintro t1 t2 ⟨_, ⟨a, rfl⟩, rfl⟩ ⟨B, hB, rfl⟩
    exact hCDF a B hB
