-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_fixed_physical_Taylor_error_measurable_of_evaluations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:58:46.637106+00:00
-- url     : https://prove2.me/submissions/a832001d-6f68-45f0-bf2a-079647b60f67

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual deterministic physical-grid X/D/J/Y C1 Taylor error is
a.e. strongly measurable from the three original evaluation families. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hderiv : Measurable (deriv w))
    (q : ℝ) (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hXeval : ∀ m i, AEStronglyMeasurable
      (fun ω => X.X (u m i) ω) P)
    (hDeval : ∀ m i, AEStronglyMeasurable
      (fun ω => rightLimit D (u m i) ω) P)
    (hJeval : ∀ m i, AEStronglyMeasurable
      (fun ω => ∑' v : ℝ≥0, if 0 < v ∧ v ≤ u m i then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0) P)
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
       ∑ i ∈ Finset.range (k m),
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
  have hY (m i : ℕ) : AEStronglyMeasurable (Y (u m i)) P :=
    (hXeval m i).add (hJeval m i)
  have hz (m i : ℕ) : AEStronglyMeasurable (z m i) P :=
    (aestronglyMeasurable_const.add (hXeval m i)).sub (hDeval m i)
  have hc (m i : ℕ) : AEStronglyMeasurable (c m i) P :=
    (hY m (i + 1)).sub (hY m i)
  have hwz (m i : ℕ) :
      AEStronglyMeasurable (fun ω => w (z m i ω)) P :=
    (hw.comp_aemeasurable (hz m i).aemeasurable).aestronglyMeasurable
  have hwzc (m i : ℕ) :
      AEStronglyMeasurable (fun ω => w (z m i ω + c m i ω)) P :=
    (hw.comp_aemeasurable ((hz m i).add (hc m i)).aemeasurable).aestronglyMeasurable
  have hd (m i : ℕ) :
      AEStronglyMeasurable (fun ω => deriv w (z m i ω)) P :=
    (hderiv.comp_aemeasurable (hz m i).aemeasurable).aestronglyMeasurable
  intro m
  have hsum' : AEStronglyMeasurable
      (∑ i ∈ Finset.range (k m), fun ω =>
        Real.exp (-(q * (u m i : ℝ))) *
          (w (z m i ω + c m i ω) - w (z m i ω) -
            deriv w (z m i ω) * c m i ω)) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i hi
    exact aestronglyMeasurable_const.mul
      (((hwzc m i).sub (hwz m i)).sub ((hd m i).mul (hc m i)))
  have hsum : AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range (k m),
        Real.exp (-(q * (u m i : ℝ))) *
          (w (z m i ω + c m i ω) - w (z m i ω) -
            deriv w (z m i ω) * c m i ω)) P := by
    have hsumEq : (fun ω =>
        ∑ i ∈ Finset.range (k m),
          Real.exp (-(q * (u m i : ℝ))) *
            (w (z m i ω + c m i ω) - w (z m i ω) -
              deriv w (z m i ω) * c m i ω)) =
          (∑ i ∈ Finset.range (k m), fun ω =>
            Real.exp (-(q * (u m i : ℝ))) *
              (w (z m i ω + c m i ω) - w (z m i ω) -
                deriv w (z m i ω) * c m i ω)) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [hsumEq]
    exact hsum'
  have heq : (fun ω => ∑ i ∈ Finset.range (k m),
        Real.exp (-(q * (u m i : ℝ))) *
          (w (z m i ω + c m i ω) - w (z m i ω) -
            deriv w (z m i ω) * c m i ω)) = Err m := by
    funext ω
    simpa only [z, c, Y, J] using (hSource m ω).symm
  simpa only [heq] using hsum
