-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_random_stopped_physical_Taylor_error_true_AE_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:17:44.441998+00:00
-- url     : https://prove2.me/submissions/a3124390-68e4-4b9d-b5fa-f4778a56c7ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_measurable_random_stopped_prefix_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original BV C1 source error summed over the true random stopped
physical-grid prefix is a.e. strongly measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hderiv : Measurable (deriv w))
    (q : ℝ) (u : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (k : ℕ → Ω → ℕ) (hk : ∀ m, Measurable (k m))
    (hBound : ∀ m ω, k m ω ≤ N m)
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       ∑ i ∈ Finset.range (k m ω),
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i))) :
    ∀ m, AEStronglyMeasurable (Err m) P := by
  let J : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω + J t ω
  let z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    x + X.X (u m i) ω - rightLimit D (u m i) ω
  let c : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    Y (u m (i + 1)) ω - Y (u m i) ω
  let f : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    Real.exp (-(q * (u m i : ℝ))) *
      (w (z m i ω + c m i ω) - w (z m i ω) -
        deriv w (z m i ω) * c m i ω)
  have hXeval (m i : ℕ) :
      AEStronglyMeasurable (fun ω => X.X (u m i) ω) P :=
    ((X.adapted (u m i)).mono (𝓕.le (u m i)) le_rfl).aestronglyMeasurable
  have hDeval (m i : ℕ) :
      AEStronglyMeasurable (fun ω => rightLimit D (u m i) ω) P :=
    (dividendStrategy_rightLimit_measurable D hD.1.1 (u m i)).aestronglyMeasurable
  have hJeval (m i : ℕ) : AEStronglyMeasurable (J (u m i)) P :=
    avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
      X hX hBV (u m i)
  have hz (m i : ℕ) : AEStronglyMeasurable (z m i) P :=
    (aestronglyMeasurable_const.add (hXeval m i)).sub (hDeval m i)
  have hc (m i : ℕ) : AEStronglyMeasurable (c m i) P :=
    ((hXeval m (i + 1)).add (hJeval m (i + 1))).sub
      ((hXeval m i).add (hJeval m i))
  have hf (m i : ℕ) : AEStronglyMeasurable (f m i) P := by
    have h1 := (hw.comp_aemeasurable ((hz m i).add (hc m i)).aemeasurable).aestronglyMeasurable
    have h2 := (hw.comp_aemeasurable (hz m i).aemeasurable).aestronglyMeasurable
    have h3 := (hderiv.comp_aemeasurable (hz m i).aemeasurable).aestronglyMeasurable
    exact aestronglyMeasurable_const.mul
      ((h1.sub h2).sub (h3.mul (hc m i)))
  intro m
  have hm := avram_bv_error7_measurable_random_stopped_prefix_sum
    (N m) (k m) (hk m) (hBound m) (f m) (hf m)
  have heq : (fun ω => ∑ i ∈ Finset.range (k m ω),
        f m i ω) = Err m := by
    funext ω
    simpa only [f, z, c, Y, J] using (hSource m ω).symm
  simpa only [heq] using hm
