-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_esscher_reflected_finite_marginal_inner_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:37:10.841431+00:00
-- url     : https://prove2.me/submissions/071a6e5e-4eb5-4789-869b-5a697ede60cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted
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
    ∀ (I : Finset ℝ≥0) (A : Set (I → ℝ × ℝ)),
      MeasurableSet A → ∀ (ε : ℝ≥0∞), 0 < ε →
      ∃ K : Set (I → ℝ × ℝ),
        IsCompact K ∧ K ⊆ A ∧
        (Measure.map
          (fun ω : Ω => fun i : I =>
            (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
          (P.withDensity (fun ω => ENNReal.ofReal
            (Real.exp (φ * X.X ((I.sup id) + 1) ω -
              ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) A
        <
        (Measure.map
          (fun ω : Ω => fun i : I =>
            (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
          (P.withDensity (fun ω => ENNReal.ofReal
            (Real.exp (φ * X.X ((I.sup id) + 1) ω -
              ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) K + ε := by
  intro I A hA ε hε
  have hfun : barrierStrategy X 0 0 = fun t ω => runningSup X t ω := by
    funext t ω
    exact barrierStrategy_self_eq_runningSup X 0 ω t
  have hadapt : Adapted 𝓕 (fun t ω => runningSup X t ω) := by
    simpa only [hfun] using barrierStrategy_adapted X 0
  have hY : Measurable (fun ω : Ω => fun i : I =>
      (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    have hs : Measurable (fun ω : Ω => runningSup X (i : ℝ≥0) ω) :=
      (hadapt (i : ℝ≥0)).mono (𝓕.le (i : ℝ≥0)) le_rfl
    have hr : Measurable (fun ω : Ω => reflectedSup X (i : ℝ≥0) ω) :=
      (reflectedSup_adapted X (i : ℝ≥0)).mono (𝓕.le (i : ℝ≥0)) le_rfl
    exact hs.prodMk hr
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
  let ν : Measure (I → ℝ × ℝ) :=
    Measure.map (fun ω : Ω => fun i : I =>
      (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω)) Q
  haveI : IsProbabilityMeasure Q := hQ
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  haveI : ν.InnerRegular := inferInstance
  obtain ⟨K, hKA, hK, hbound⟩ :=
    hA.exists_isCompact_lt_add (measure_lt_top ν A).ne hε.ne'
  refine ⟨K, hK, hKA, ?_⟩
  simpa [ν, Q, T] using hbound
