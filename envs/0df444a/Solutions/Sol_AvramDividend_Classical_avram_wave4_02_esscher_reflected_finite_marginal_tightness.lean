-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_esscher_reflected_finite_marginal_tightness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:49:01.275675+00:00
-- url     : https://prove2.me/submissions/864c35a7-2ad5-460b-9110-afa641cca222

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

/-- Tightness of each actual finite-dimensional Esscher-reflected law.
The compact witness is source-specific; this does not assert a path-space law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ (I : Finset ℝ≥0) (ε : ℝ≥0∞), 0 < ε →
      ∃ K : Set (I → ℝ × ℝ),
        IsCompact K ∧
          (Measure.map
            (fun ω : Ω => fun i : I =>
              (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
            (P.withDensity (fun ω => ENNReal.ofReal
              (Real.exp (φ * X.X ((I.sup id) + 1) ω -
                ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) Kᶜ ≤ ε := by
  intro I ε hε
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
  have hQ : IsProbabilityMeasure Q := by
    exact esscher_bounded_stop_density_probability
      X φ (le_of_lt hφ) (fun _ : Ω => T)
      hstop T (fun _ => le_rfl) (T + 1) le_rfl
  let ν : Measure (I → ℝ × ℝ) :=
    Measure.map (fun ω : Ω => fun i : I =>
      (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω)) Q
  haveI : IsProbabilityMeasure Q := hQ
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  have hTight : IsTightMeasureSet
      ({ν} : Set (Measure (I → ℝ × ℝ))) :=
    isTightMeasureSet_singleton
  obtain ⟨K, hK, hbound⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le).mp hTight ε hε
  refine ⟨K, hK, ?_⟩
  simpa [ν, Q, T] using hbound ν (by simp)
