-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys54_intrinsic_signed_kernel_integral_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:18:39.64627+00:00
-- url     : https://prove2.me/submissions/11e46020-a3c5-445f-9096-1aabe170775b

import Mathlib.Probability.Process.Predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Ordinary s-finite kernel integration makes the original signed marked integral measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (F : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hFm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] F) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    (∀ᵐ ω ∂P, Integrable
       (fun p : ℝ≥0 × ℝ => F ((p.1, ω), p.2)) (NX ω)) →
    AEStronglyMeasurable
      (fun ω => ∫ p, F ((p.1, ω), p.2) ∂(NX ω)) P := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
  change (∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => F ((p.1, ω), p.2)) (NX ω)) →
    AEStronglyMeasurable
      (fun ω => ∫ p, F ((p.1, ω), p.2) ∂(NX ω)) P
  intro _hFibre
  have hPredictableLe :
      𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      have hA' : MeasurableSet A :=
        (𝓕.rightCont.le (⊥ : ℝ≥0)) A hA
      exact (measurableSet_singleton (⊥ : ℝ≥0)).prod hA'
    · intro i A hA
      have hA' : MeasurableSet A :=
        (𝓕.rightCont.le i) A hA
      exact (measurableSet_Ioi :
        MeasurableSet (Ioi i)).prod hA'
  have hProdLe :
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) ≤
      (inferInstance : MeasurableSpace ((ℝ≥0 × Ω) × ℝ)) := by
    change (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ) ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)).prod
        (inferInstance : MeasurableSpace ℝ)
    unfold MeasurableSpace.prod
    exact sup_le_sup (MeasurableSpace.comap_mono hPredictableLe) le_rfl
  have hOrdinary : Measurable F := hFm.mono hProdLe le_rfl
  have hReorder : Measurable
      (fun p : Ω × (ℝ≥0 × ℝ) => ((p.2.1, p.1), p.2.2)) := by
    fun_prop
  have hJoint : StronglyMeasurable
      (fun p : Ω × (ℝ≥0 × ℝ) => F ((p.2.1, p.1), p.2.2)) :=
    (hOrdinary.comp hReorder).stronglyMeasurable
  obtain ⟨κ, hκ, hκeq⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  letI : ProbabilityTheory.IsSFiniteKernel κ := hκ
  have hIntegral : StronglyMeasurable
      (fun ω => ∫ p, F ((p.1, ω), p.2) ∂(κ ω)) := by
    exact StronglyMeasurable.integral_kernel_prod_right'
      (κ := κ) hJoint
  have hIntegral' : StronglyMeasurable
      (fun ω => ∫ p, F ((p.1, ω), p.2) ∂(NX ω)) := by
    simpa only [hκeq] using hIntegral
  exact hIntegral'.aestronglyMeasurable
