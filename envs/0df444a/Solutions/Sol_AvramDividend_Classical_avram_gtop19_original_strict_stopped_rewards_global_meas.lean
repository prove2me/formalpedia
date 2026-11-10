-- Prove2me | solution 1 for AvramDividend.Classical.avram_gtop19_original_strict_stopped_rewards_global_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T01:39:04.530974+00:00
-- url     : https://prove2.me/submissions/71a54391-d561-4527-a6ba-aab1800591cd

import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσle : ∀ ω, σ ω ≤ τ ω)
    (ρ : ℕ → Ω → ℝ≥0)
    (hρstop : ∀ j, IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ j ω : WithTop ℝ≥0)))
    (hρle : ∀ j ω, ρ j ω ≤ σ ω) :
    let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω =>
      if ζ ω = 0 then w x else
        Real.exp (-(q * (ζ ω : ℝ))) *
          w (riskProcess X x D (ζ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    (∀ j, Measurable (H (ρ j))) ∧ AEStronglyMeasurable (H σ) P := by
  classical
  let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω =>
    if ζ ω = 0 then w x else
      Real.exp (-(q * (ζ ω : ℝ))) *
        w (riskProcess X x D (ζ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
  change (∀ j, Measurable (H (ρ j))) ∧ AEStronglyMeasurable (H σ) P
  have hDstrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hRuinM : Measurable (ruinTime X x D) :=
    (ruinTime_stopping_rightCont_filtration X x D hDstrat).measurable'
  have hwM : Measurable w :=
    avram_wave6_04b_cap_extension_measurable_of_zero_negative w w C hw_cont hw_neg
      (by intro _ _; rfl) (by intro h; exact False.elim (h hTopCap))
  have hMeas (ζ : Ω → ℝ≥0)
      (hζstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ζ ω : WithTop ℝ≥0))) :
      Measurable (H ζ) := by
    have hζENN : Measurable (fun ω : Ω => (ζ ω : WithTop ℝ≥0)) :=
      hζstop.measurable'
    have hζNN : Measurable ζ := measurable_coe_nnreal_ennreal_iff.mp hζENN
    have hζR : Measurable (fun ω : Ω => (ζ ω : ℝ)) := hζNN.coe_nnreal_real
    have hY : Measurable (fun ω : Ω =>
        riskProcess X x D (ζ ω) ω) := by
      have hJoint :=
        avram_p3_g2_original_prepayment_riskProcess_joint_measurable
          X x D hDstrat
      exact hJoint.comp (hζNN.prodMk measurable_id)
    have hExp : Measurable (fun ω : Ω =>
        Real.exp (-(q * (ζ ω : ℝ)))) :=
      Real.continuous_exp.measurable.comp
        ((measurable_const.mul hζR).neg)
    have hTerm : Measurable (fun ω : Ω =>
        Real.exp (-(q * (ζ ω : ℝ))) *
          w (riskProcess X x D (ζ ω) ω)) :=
      hExp.mul (hwM.comp hY)
    let E : Ω → Set ℝ := fun ω =>
      paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ)
    have hE (ω : Ω) : MeasurableSet (E ω) :=
      (paymentTimes_measurable (ruinTime X x D ω)).inter measurableSet_Iio
    let A : Set (ℝ × Ω) :=
      {p | p.1 ∈ paymentTimes (ruinTime X x D p.2) ∧
        p.1 < (ζ p.2 : ℝ)}
    have hA : MeasurableSet A :=
      (paymentTimes_joint_measurable (ruinTime X x D) hRuinM).inter
        (measurableSet_lt measurable_fst (hζR.comp measurable_snd))
    let W : ℝ → ℝ≥0∞ := fun t =>
      ENNReal.ofReal (Real.exp (-(q * t)))
    have hW : Measurable W := ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp ((measurable_const.mul measurable_id).neg))
    obtain ⟨κ, hκs, hκ⟩ :=
      dividendMeasure_global_sfinite_kernel_exists D hDstrat
    letI : IsSFiniteKernel κ := hκs
    have hKernel := measurable_random_indicator_lintegral κ A hA W hW
    have hEq : (fun ω : Ω =>
        ∫⁻ t in E ω, W t ∂dividendMeasure D ω) =
        (fun ω : Ω =>
          ∫⁻ t, if (t, ω) ∈ A then W t else 0 ∂κ ω) := by
      funext ω
      rw [hκ ω, ← lintegral_indicator (hE ω) W]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ E ω
      · have htA : (t, ω) ∈ A := ht
        simp [Set.indicator, ht, htA]
      · have htA : (t, ω) ∉ A := fun hs => ht hs
        simp [Set.indicator, ht, htA]
    have hCashENN : Measurable (fun ω : Ω =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) := by
      change Measurable (fun ω : Ω =>
        ∫⁻ t in E ω, W t ∂dividendMeasure D ω)
      rw [hEq]
      simpa only [A, Set.mem_setOf_eq] using hKernel
    have hCash : Measurable (fun ω : Ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) :=
      ENNReal.measurable_toReal.comp hCashENN
    have hZero : MeasurableSet {ω : Ω | ζ ω = 0} := (measurableSet_singleton (0 : ℝ≥0)).preimage hζNN
    have hPiece : Measurable (fun ω : Ω => if ζ ω = 0 then w x else
        Real.exp (-(q * (ζ ω : ℝ))) * w (riskProcess X x D (ζ ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) := by
      exact Measurable.ite hZero (measurable_const : Measurable (fun _ : Ω => w x)) (hTerm.add hCash)
    exact hPiece
  exact ⟨fun j => hMeas (ρ j) (hρstop j), (hMeas σ hσstop).aestronglyMeasurable⟩
