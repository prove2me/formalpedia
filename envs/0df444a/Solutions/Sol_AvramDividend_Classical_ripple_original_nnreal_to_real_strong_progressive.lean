-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_nnreal_to_real_strong_progressive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:46:48.420073+00:00
-- url     : https://prove2.me/submissions/89f1faf7-cbc8-4d51-b8d7-d15c3c070d31

import Mathlib
open MeasureTheory Set
open scoped NNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (Fr : Filtration ℝ mΩ)
    (hFr : ∀ t : ℝ, Fr t = F (Real.toNNReal t))
    (G : ℝ≥0 → Ω → ℝ)
    (hG : IsStronglyProgressive F G) :
    IsStronglyProgressive Fr
      (fun t ω => G (Real.toNNReal t) ω) := by
  intro t
  letI : MeasurableSpace Ω := F (Real.toNNReal t)
  let e : Set.Iic t × Ω → Set.Iic (Real.toNNReal t) × Ω := fun p =>
    (⟨Real.toNNReal (p.1 : ℝ), Real.toNNReal_mono p.1.property⟩, p.2)
  have ht : Measurable (fun a : Set.Iic t =>
      (⟨Real.toNNReal (a : ℝ), Real.toNNReal_mono a.property⟩ :
        Set.Iic (Real.toNNReal t))) :=
    (measurable_real_toNNReal.comp measurable_subtype_coe).subtype_mk
  have he : Measurable e := (ht.comp measurable_fst).prodMk measurable_snd
  have hSource : StronglyMeasurable
      (fun p : Set.Iic (Real.toNNReal t) × Ω => G p.1 p.2) :=
    hG (Real.toNNReal t)
  have hResult : StronglyMeasurable
      (fun p : Set.Iic t × Ω => G (Real.toNNReal (p.1 : ℝ)) p.2) := by
    exact hSource.comp_measurable he
  rw [hFr t]
  exact hResult
