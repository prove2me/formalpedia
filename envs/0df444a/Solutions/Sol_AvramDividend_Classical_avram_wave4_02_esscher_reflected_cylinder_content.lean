-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_esscher_reflected_cylinder_content
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:47:01.760284+00:00
-- url     : https://prove2.me/submissions/946c4c64-45fa-429c-a725-94d345bd8c10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_projective_family
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_density_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual Esscher-reflected finite laws induce a normalised additive
content with their exact cylinder probabilities.  No infinite-path measure
or excursion point-process compensator is assumed or asserted. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ C : AddContent ℝ≥0∞
        (measurableCylinders (fun _ : ℝ≥0 => ℝ × ℝ)),
      C Set.univ = 1 ∧
        ∀ (I : Finset ℝ≥0) (A : Set (I → ℝ × ℝ)),
          MeasurableSet A →
            C (cylinder I A) =
              (Measure.map
                (fun ω : Ω => fun i : I =>
                  (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
                (P.withDensity (fun ω => ENNReal.ofReal
                  (Real.exp (φ * X.X ((I.sup id) + 1) ω -
                    ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) A := by
  let F : (I : Finset ℝ≥0) → Measure (I → ℝ × ℝ) := fun I =>
    Measure.map
      (fun ω : Ω => fun i : I =>
        (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X ((I.sup id) + 1) ω -
          ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))
  have hF : IsProjectiveMeasureFamily
      (α := fun _ : ℝ≥0 => ℝ × ℝ) F :=
    avram_wave4_02_esscher_reflected_projective_family
      X q hq φ hφ hroot
  let C : AddContent ℝ≥0∞
      (measurableCylinders (fun _ : ℝ≥0 => ℝ × ℝ)) :=
    projectiveFamilyContent hF
  have hstop : IsStoppingTime 𝓕
      (fun _ : Ω => ((1 : ℝ≥0) : WithTop ℝ≥0)) := by
    intro s
    by_cases hs : (1 : ℝ≥0) ≤ s
    · simp [hs]
    · simp [hs]
  have hQ : IsProbabilityMeasure
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X (1 : ℝ≥0) ω -
          (1 : ℝ) * X.ψ φ)))) :=
    esscher_bounded_stop_density_probability
      X φ (le_of_lt hφ) (fun _ : Ω => (1 : ℝ≥0))
      hstop 1 (fun _ => le_rfl) 2 (by norm_num)
  have hY0 : Measurable
      (fun ω : Ω => fun i : (∅ : Finset ℝ≥0) =>
        (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω)) := by
    exact measurable_of_subsingleton_codomain _
  have hF0 : (F ∅) Set.univ = 1 := by
    dsimp [F]
    simp only [Finset.sup_empty, zero_add]
    rw [Measure.map_apply hY0 MeasurableSet.univ]
    simpa using hQ.measure_univ
  refine ⟨C, ?_, ?_⟩
  · have hC := projectiveFamilyContent_cylinder
        (I := (∅ : Finset ℝ≥0)) (S := Set.univ)
        hF MeasurableSet.univ
    simpa only [C, cylinder_univ] using hC.trans hF0
  · intro I A hA
    exact projectiveFamilyContent_cylinder hF hA
