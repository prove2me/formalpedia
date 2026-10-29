-- Prove2me | solution 1 for AvramDividend.Classical.levy_linear_drift_shift_increment_laws_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:07:41.253565+00:00
-- url     : https://prove2.me/submissions/f394641a-7f7a-48cd-a7a0-760341a51970

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (C : ℝ) :
    ∀ (s t : ℝ≥0), s ≤ t →
      Indep
        (MeasurableSpace.comap
          (fun ω : Ω => (X.X t ω - C * (t : ℝ)) -
            (X.X s ω - C * (s : ℝ))) inferInstance)
        (𝓕 s) P ∧
      IdentDistrib
        (fun ω : Ω => (X.X t ω - C * (t : ℝ)) -
          (X.X s ω - C * (s : ℝ)))
        (fun ω : Ω => X.X (t - s) ω - C * ((t - s : ℝ≥0) : ℝ)) P P := by
  intro s t hst
  let f : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  let g : ℝ → ℝ := fun x => x - C * ((t - s : ℝ≥0) : ℝ)
  have hg : Measurable g := measurable_id.sub measurable_const
  have hF : (fun ω : Ω => (X.X t ω - C * (t : ℝ)) -
        (X.X s ω - C * (s : ℝ))) = g ∘ f := by
    funext ω
    dsimp [f, g, Function.comp_def]
    rw [NNReal.coe_sub hst]
    ring
  have hcomap : MeasurableSpace.comap f
      (MeasurableSpace.comap g inferInstance) ≤
      MeasurableSpace.comap f inferInstance :=
    MeasurableSpace.comap_mono hg.comap_le
  have hI : Indep
      (MeasurableSpace.comap (fun ω : Ω =>
        (X.X t ω - C * (t : ℝ)) - (X.X s ω - C * (s : ℝ)))
          inferInstance) (𝓕 s) P := by
    rw [hF]
    simpa only [MeasurableSpace.comap_comp] using
      (indep_of_indep_of_le_left (X.indepIncrements s t hst) hcomap)
  have hS : IdentDistrib
      (fun ω : Ω => (X.X t ω - C * (t : ℝ)) -
        (X.X s ω - C * (s : ℝ)))
      (fun ω : Ω => X.X (t - s) ω - C * ((t - s : ℝ≥0) : ℝ)) P P := by
    have hi := (X.stationaryIncrements s t hst).sub_const
      (C * ((t - s : ℝ≥0) : ℝ))
    rw [hF]
    simpa only [f, g, Function.comp_def] using hi
  exact ⟨hI, hS⟩
