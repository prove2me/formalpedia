-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_stop_sampled_survival_predictable_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:43:01.399195+00:00
-- url     : https://prove2.me/submissions/105c2679-19c0-449a-8ac0-32cf862b922f

import Mathlib.Probability.Process.Stopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
noncomputable section
/-- Original left-grid survival masks preserve predictability through the random final cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ))
    (K : Ω → ℕ)
    (hK : IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ)))
    (G H : ℕ → Ω → ℝ)
    (hG : ∀ i, Measurable[𝓕.rightCont (e i)] (G i))
    (hH : ∀ i, Measurable[𝓕.rightCont (e i)] (H i)) :
    ∀ i,
      Measurable[𝓕.rightCont (e i)]
        (fun ω => if i < K ω then G i ω else 0) ∧
      Measurable[𝓕.rightCont (e i)]
        (fun ω => if i < K ω then H i ω else 0) := by
  intro i
  have hSample :
      MeasurableSet[𝓖 i]
        {ω : Ω | (i : WithTop ℕ) < (K ω : WithTop ℕ)} :=
    hK.measurableSet_gt i
  have hSurvival : MeasurableSet[𝓕.rightCont (e i)]
      {ω : Ω | i < K ω} := by
    rw [h𝓖] at hSample
    change MeasurableSet[𝓕.rightCont (e i)]
      {ω : Ω | (i : WithTop ℕ) < (K ω : WithTop ℕ)} at hSample
    simpa using hSample
  exact ⟨Measurable.ite hSurvival (hG i) measurable_const,
    Measurable.ite hSurvival (hH i) measurable_const⟩
