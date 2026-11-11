-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_uniform_driver_on_real_sequence_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:01:51.201287+00:00
-- url     : https://prove2.me/submissions/8312ba9b-69cb-442c-95eb-38c41766f2b6

import Mathlib
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_driver_exists

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- The abstract two-stream driver transports to the fixed product of real
sequences while preserving its *infinite* joint product law. -/
theorem solution :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ),
      IsProbabilityMeasure P ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
        ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)
  obtain ⟨Ω, mΩ, μ, τ, Y, hμ, hd⟩ :=
    AvramDividend.Classical.avram_a06_uniform_negative_mark_driver_exists
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure μ := hμ
  let f : Ω → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun ω => (fun n => τ n ω, fun n => Y n ω)
  have hf : Measurable f := by
    exact (measurable_pi_iff.mpr hd.measurable_interarrival).prod
      (measurable_pi_iff.mpr hd.measurable_mark)
  let P : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := μ.map f
  letI : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map hf.aemeasurable
  let τ' : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n z => z.1 n
  let Y' : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n z => z.2 n
  have hτmeas (n : ℕ) : Measurable (τ' n) :=
    (measurable_pi_apply n).comp measurable_fst
  have hYmeas (n : ℕ) : Measurable (Y' n) :=
    (measurable_pi_apply n).comp measurable_snd
  have hsrcMarginal :
      ∀ i : ℕ ⊕ ℕ,
        HasLaw (Sum.elim τ Y i)
          (Sum.elim (fun _ : ℕ => expMeasure (1 : ℝ))
            (fun _ : ℕ => ν) i) μ := by
    rintro (n | n)
    · exact hd.law_interarrival n
    · exact hd.law_mark n
  have hsrcMeas : Measurable (fun ω i => Sum.elim τ Y i ω) := by
    apply measurable_pi_iff.mpr
    rintro (n | n)
    · exact hd.measurable_interarrival n
    · exact hd.measurable_mark n
  have hsrcJoint :
      HasLaw (fun ω i => Sum.elim τ Y i ω)
        (Measure.infinitePi (Sum.elim (fun _ : ℕ => expMeasure (1 : ℝ))
          (fun _ : ℕ => ν))) μ :=
    (iIndepFun_iff_hasLaw_Pi_infinitePi hsrcMarginal
      hsrcMeas.aemeasurable).mp hd.indep
  have htargetMarginal :
      ∀ i : ℕ ⊕ ℕ,
        HasLaw (Sum.elim τ' Y' i)
          (Sum.elim (fun _ : ℕ => expMeasure (1 : ℝ))
            (fun _ : ℕ => ν) i) P := by
    rintro (n | n)
    · refine ⟨(hτmeas n).aemeasurable, ?_⟩
      change Measure.map (τ' n) P = expMeasure (1 : ℝ)
      rw [show P = μ.map f from rfl, Measure.map_map (hτmeas n) hf]
      change Measure.map (τ n) μ = expMeasure (1 : ℝ)
      exact (hd.law_interarrival n).map_eq
    · refine ⟨(hYmeas n).aemeasurable, ?_⟩
      change Measure.map (Y' n) P = ν
      rw [show P = μ.map f from rfl, Measure.map_map (hYmeas n) hf]
      change Measure.map (Y n) μ = ν
      exact (hd.law_mark n).map_eq
  have htargetMeas : Measurable (fun z i => Sum.elim τ' Y' i z) := by
    apply measurable_pi_iff.mpr
    rintro (n | n)
    · exact hτmeas n
    · exact hYmeas n
  have htargetJoint :
      HasLaw (fun z i => Sum.elim τ' Y' i z)
        (Measure.infinitePi (Sum.elim (fun _ : ℕ => expMeasure (1 : ℝ))
          (fun _ : ℕ => ν))) P := by
    refine ⟨htargetMeas.aemeasurable, ?_⟩
    change Measure.map (fun z i => Sum.elim τ' Y' i z) P = _
    rw [show P = μ.map f from rfl, Measure.map_map htargetMeas hf]
    convert hsrcJoint.map_eq using 1
    congr 1
    funext ω i
    cases i <;> rfl
  refine ⟨P, τ', Y', inferInstance, ?_⟩
  exact
    { measurable_interarrival := hτmeas
      measurable_mark := hYmeas
      indep := (iIndepFun_iff_hasLaw_Pi_infinitePi
        htargetMarginal htargetMeas.aemeasurable).mpr htargetJoint
      law_interarrival := fun n => htargetMarginal (Sum.inl n)
      law_mark := fun n => htargetMarginal (Sum.inr n) }
