-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_esscher_reflected_cylinder_compact_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:51:47.836993+00:00
-- url     : https://prove2.me/submissions/f25d2a15-5e56-453b-883d-38b84a0d2f92

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_cylinder_content
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_finite_marginal_inner_regular
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_density_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ C : AddContent ℝ≥0∞
        (measurableCylinders (fun _ : ℝ≥0 => ℝ × ℝ)),
      C Set.univ = 1 ∧
        (∀ (I : Finset ℝ≥0) (A : Set (I → ℝ × ℝ)),
          MeasurableSet A →
            C (cylinder I A) =
              (Measure.map
                (fun ω : Ω => fun i : I =>
                  (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
                (P.withDensity (fun ω => ENNReal.ofReal
                  (Real.exp (φ * X.X ((I.sup id) + 1) ω -
                    ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) A) ∧
        (∀ (s : Set (ℝ≥0 → ℝ × ℝ)),
          s ∈ measurableCylinders (fun _ : ℝ≥0 => ℝ × ℝ) →
            ∀ (ε : ℝ≥0∞), 0 < ε →
              ∃ F : Set (ℝ≥0 → ℝ × ℝ),
                F ∈ closedCompactCylinders (fun _ : ℝ≥0 => ℝ × ℝ) ∧
                F ⊆ s ∧ C (s \ F) < ε) := by
  obtain ⟨C, hCuniv, hC⟩ :=
    avram_wave4_02_esscher_reflected_cylinder_content X q hq φ hφ hroot
  refine ⟨C, hCuniv, hC, ?_⟩
  intro s hs ε hε
  obtain ⟨I, A, hA, rfl⟩ := (mem_measurableCylinders s).mp hs
  obtain ⟨K, hKcompact, hKA, hbound⟩ :=
    avram_wave4_02_esscher_reflected_finite_marginal_inner_regular
      X q hq φ hφ hroot I A hA ε hε
  have hKclosed : IsClosed K := hKcompact.isClosed
  let ν : Measure (I → ℝ × ℝ) :=
    Measure.map
      (fun ω : Ω => fun i : I =>
        (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X ((I.sup id) + 1) ω -
          ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))
  have hdiff : ν (A \ K) < ε :=
    measure_sdiff_lt_of_lt_add
      hKclosed.nullMeasurableSet hKA (by
        let T : ℝ≥0 := I.sup id + 1
        let Q : Measure Ω :=
          P.withDensity (fun ω => ENNReal.ofReal
            (Real.exp (φ * X.X T ω - (T : ℝ) * X.ψ φ)))
        have hstop : IsStoppingTime 𝓕
            (fun _ : Ω => (T : WithTop ℝ≥0)) := by
          intro s
          by_cases hs : T ≤ s
          · simp [hs]
          · simp [hs]
        have hQ : IsProbabilityMeasure Q :=
          esscher_bounded_stop_density_probability
            X φ (le_of_lt hφ) (fun _ : Ω => T)
            hstop T (fun _ => le_rfl) (T + 1) le_rfl
        haveI : IsProbabilityMeasure Q := hQ
        haveI : IsFiniteMeasure ν := by
          change IsFiniteMeasure (Measure.map
            (fun ω : Ω => fun i : I =>
              (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω)) Q)
          exact Measure.isFiniteMeasure_map Q _
        exact (measure_lt_top ν K).ne) hbound
  refine ⟨cylinder I K, ?_, ?_, ?_⟩
  · exact cylinder_mem_closedCompactCylinders
      (X := fun _ : ℝ≥0 => ℝ × ℝ) I K hKclosed hKcompact
  · exact preimage_mono hKA
  · rw [sdiff_cylinder_same]
    rw [hC I (A \ K) (hA.diff hKclosed.measurableSet)]
    exact hdiff
