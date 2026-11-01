-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_esscher_reflected_projective_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:18:23.270427+00:00
-- url     : https://prove2.me/submissions/fc7360b0-4bf3-49db-96b6-222196a8f6fa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_finset_projective_law
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Genuine finite-dimensional projectivity of the Esscher laws of the actual
reflected Lévy process, with the source record local time as the first coordinate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    IsProjectiveMeasureFamily (α := fun _ : ℝ≥0 => ℝ × ℝ)
      (fun I : Finset ℝ≥0 =>
        Measure.map
          (fun ω : Ω => fun i : I =>
            (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
          (P.withDensity (fun ω => ENNReal.ofReal
            (Real.exp (φ * X.X ((I.sup id) + 1) ω -
              ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) := by
  have hfun : barrierStrategy X 0 0 = fun t ω => runningSup X t ω := by
    funext t ω
    exact barrierStrategy_self_eq_runningSup X 0 ω t
  have hadapt : Adapted 𝓕 (fun t ω => runningSup X t ω) := by
    simpa only [hfun] using barrierStrategy_adapted X 0
  have hmeas (I : Finset ℝ≥0) :
      Measurable (fun ω : Ω => fun i : I =>
        (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    have hs : Measurable (fun ω : Ω => runningSup X (i : ℝ≥0) ω) :=
      (hadapt (i : ℝ≥0)).mono (𝓕.le (i : ℝ≥0)) le_rfl
    have hr : Measurable (fun ω : Ω => reflectedSup X (i : ℝ≥0) ω) :=
      (reflectedSup_adapted X (i : ℝ≥0)).mono (𝓕.le (i : ℝ≥0)) le_rfl
    exact hs.prodMk hr
  intro I J hJI
  have hJ : ∀ t ∈ J, t ≤ J.sup id := by
    intro t ht
    exact Finset.le_sup (f := id) ht
  have hsup : J.sup id ≤ I.sup id := Finset.sup_mono hJI
  have hT : (J.sup id) + 1 ≤ (I.sup id) + 1 :=
    add_le_add_left hsup 1
  have hcons :=
    avram_wave4_02_esscher_reflected_finset_projective_law
      X q hq φ hφ hroot J (J.sup id) ((J.sup id) + 1)
      ((I.sup id) + 1) hJ le_rfl hT
  have hres : Measurable
      (fun f : I → ℝ × ℝ => fun j : J =>
        f (⟨(j : ℝ≥0), hJI j.property⟩ : I)) := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (⟨(j : ℝ≥0), hJI j.property⟩ : I)
  calc
    Measure.map
      (fun ω : Ω => fun j : J =>
        (runningSup X (j : ℝ≥0) ω, reflectedSup X (j : ℝ≥0) ω))
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X ((J.sup id) + 1) ω -
          ((((J.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ)))) =
      Measure.map
        (fun ω : Ω => fun j : J =>
          (runningSup X (j : ℝ≥0) ω, reflectedSup X (j : ℝ≥0) ω))
        (P.withDensity (fun ω => ENNReal.ofReal
          (Real.exp (φ * X.X ((I.sup id) + 1) ω -
            ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ)))) := hcons
    _ = Measure.map
      (fun f : I → ℝ × ℝ => fun j : J =>
        f (⟨(j : ℝ≥0), hJI j.property⟩ : I))
      (Measure.map
        (fun ω : Ω => fun i : I =>
          (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
        (P.withDensity (fun ω => ENNReal.ofReal
          (Real.exp (φ * X.X ((I.sup id) + 1) ω -
            ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) := by
      rw [Measure.map_map hres (hmeas I)]
      rfl
