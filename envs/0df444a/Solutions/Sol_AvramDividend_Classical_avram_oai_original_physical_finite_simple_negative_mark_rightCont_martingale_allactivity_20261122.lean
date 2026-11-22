-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_physical_finite_simple_negative_mark_rightCont_martingale_allactivity_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:13:29.69532+00:00
-- url     : https://prove2.me/submissions/61f0dde7-c8d9-4a32-a4e7-177c4a42d9ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_mark_count_process_rightcont_stronglyAdapted_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_mark_compensated_process_L1_allactivity_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_compensated_simple_mark_time_additivity_allactivity_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_mark_condExp_all_strict_time_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (hν : X.ν S < ⊤) (g : SimpleFunc ℝ ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let F : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc 0 t ×ˢ B y)).toReal -
          (((t : ℝ≥0∞) * X.ν (B y))).toReal)
    Martingale F 𝓕.rightCont P  := by
  classical
  intro NX B F
  have hAdapt : StronglyAdapted 𝓕.rightCont F := by
    simpa only [F, NX, B] using
      (avram_oai_original_physical_simple_mark_count_process_rightcont_stronglyAdapted_20261122
        X S hS g)
  have hInt : ∀ t, Integrable (F t) P := by
    intro t
    simpa only [F, NX, B] using
      (avram_oai_original_physical_simple_mark_compensated_process_L1_allactivity_20261122
        X t S hS hNeg hν g)
  refine ⟨hAdapt, ?_⟩
  intro s t hst
  by_cases heq : s = t
  · subst t
    have hCE : condExp (𝓕.rightCont s) P (F s) = F s :=
      condExp_of_stronglyMeasurable
        (𝓕.rightCont.le s) (hAdapt s) (hInt s)
    exact Filter.EventuallyEq.of_eq hCE
  · have hlt : s < t := lt_of_le_of_ne hst heq
    let G : Ω → ℝ := fun ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc s t ×ˢ B y)).toReal -
          ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B y))).toReal)
    have hSplit : F t =ᵐ[P] (fun ω => F s ω + G ω) := by
      have hRaw :=
        avram_oai_original_physical_compensated_simple_mark_time_additivity_allactivity_20261122
          X s t hst S hS hNeg hν g
      filter_upwards [hRaw] with ω hw
      exact hw
    have hCond : condExp (𝓕.rightCont s) P G =ᵐ[P]
        (fun _ => (0 : ℝ)) := by
      simpa only [G, NX, B] using
        (avram_oai_original_physical_simple_mark_condExp_all_strict_time_20261122
          X s t hlt S hS hν g)
    have hIntG : Integrable G P := by
      have hEq : G =ᵐ[P] (fun ω => F t ω - F s ω) := by
        filter_upwards [hSplit] with ω hw
        rw [hw]
        ring
      exact ((hInt t).sub (hInt s)).congr hEq.symm
    have hFs : condExp (𝓕.rightCont s) P (F s) = F s :=
      condExp_of_stronglyMeasurable
        (𝓕.rightCont.le s) (hAdapt s) (hInt s)
    calc
      condExp (𝓕.rightCont s) P (F t) =ᵐ[P]
          condExp (𝓕.rightCont s) P
            (fun ω => F s ω + G ω) :=
        condExp_congr_ae hSplit
      _ =ᵐ[P] (fun ω =>
          condExp (𝓕.rightCont s) P (F s) ω +
          condExp (𝓕.rightCont s) P G ω) :=
        condExp_add (hInt s) hIntG (𝓕.rightCont s)
      _ =ᵐ[P] F s := by
        filter_upwards [hCond] with ω hw
        rw [hFs, hw]
        simp
