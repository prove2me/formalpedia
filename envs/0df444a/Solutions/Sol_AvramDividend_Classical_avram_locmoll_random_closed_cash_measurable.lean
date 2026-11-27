-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_random_closed_cash_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:16:23.596328+00:00
-- url     : https://prove2.me/submissions/7cba890d-14a4-49d6-ace7-b59649517058

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (θ : Ω → ℝ≥0)
    (hθ : IsStoppingTime 𝓕.rightCont (fun ω => (θ ω : WithTop ℝ≥0))) :
    AEMeasurable (fun ω => ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) P := by 
  classical
  obtain ⟨κ, hκ, heq⟩ := dividendMeasure_global_sfinite_kernel_exists D hD
  letI : ProbabilityTheory.IsSFiniteKernel κ := hκ
  have ht : Measurable θ := by
    apply measurable_of_Iic
    intro a
    have he : θ ⁻¹' Iic a = {ω | (θ ω : WithTop ℝ≥0) ≤ a} := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_setOf_eq, WithTop.coe_le_coe]
    rw [he]
    exact 𝓕.rightCont.le a _ (hθ a)
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  have hf : Measurable f := by dsimp [f]; fun_prop
  let E : Ω → Set ℝ := fun ω => paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ)
  let S : Set (ℝ × Ω) := {p | p.1 ∈ E p.2}
  have hE (ω : Ω) : MeasurableSet (E ω) := by
    dsimp [E, paymentTimes]; measurability
  have hS : MeasurableSet S := by
    have hEq : S = {p : ℝ × Ω | p.1 ∈ paymentTimes (ruinTime X x D p.2)} ∩
        {p : ℝ × Ω | p.1 ≤ (θ p.2 : ℝ)} := by
      ext p
      simp [S, E]
    rw [hEq]
    exact (paymentTimes_joint_measurable _ (ruinTime_measurable X x D hD)).inter
      (measurableSet_le measurable_fst ((measurable_subtype_coe : Measurable (fun a : ℝ≥0 => (a : ℝ))).comp (ht.comp measurable_snd)))
  have hKernel := measurable_random_indicator_lintegral κ S hS f hf
  have hEq : (fun ω : Ω => ∫⁻ t in E ω, f t ∂(dividendMeasure D ω)) =
      (fun ω : Ω => ∫⁻ t, if (t, ω) ∈ S then f t else 0 ∂κ ω) := by
    funext ω
    rw [heq ω, ← lintegral_indicator (hE ω) f]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ E ω
    · have hs : (t, ω) ∈ S := ht
      simp [Set.indicator, ht, hs]
    · have hs : (t, ω) ∉ S := ht
      simp [Set.indicator, ht, hs]
  change AEMeasurable (fun ω : Ω => ∫⁻ t in E ω, f t ∂(dividendMeasure D ω)) P
  rw [hEq]
  simpa only [S, Set.mem_setOf_eq] using hKernel.aemeasurable (μ := P)
