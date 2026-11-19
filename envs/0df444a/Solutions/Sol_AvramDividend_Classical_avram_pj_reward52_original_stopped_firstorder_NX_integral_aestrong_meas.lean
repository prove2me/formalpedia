-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward52_original_stopped_firstorder_NX_integral_aestrong_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:32:58.780656+00:00
-- url     : https://prove2.me/submissions/47885f85-df11-4c19-bc00-1469affbc875

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward66_original_stopped_firstorder_clock_joint_kernel_meas
set_option pp.universes true

set_option pp.explicit true
set_option pp.fullNames true
open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hSigmaZero : X.σ = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (G : Ω → ℝ) (hGdef : ∀ ω, G ω = (if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)) (hGI : Integrable G P) (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) (Cband u v δ η : ℝ)
    (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (huv : u + δ < v) (hη : 0 < η) (hη1 : η < 1)
    (hv : v < Cband) (hvC : v < C.toReal)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband)) :
      (let T : ℝ≥0 := (n : ℝ≥0)
      let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
          (fun s : ℝ≥0 => (s, X.X s ω -
            Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
      let Lsource : Ω → ℝ := fun ω =>
        (∫ p, (if p.1 ≤ ρ ω ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if Y (p.1, ω) ∈ Icc (u + δ) v then
              deriv w (Y (p.1, ω)) * p.2 else 0) else 0) ∂(NX ω))
      AEStronglyMeasurable Lsource P) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
      Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
      (fun s : ℝ≥0 => (s, X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun s => x + X.X s p.2 - rightLimit D s p.2) p.1
  let F : Ω × (ℝ≥0 × ℝ) → ℝ := fun p =>
    if p.2.1 ≤ ρ p.1 ∧ p.2.2 ∈ Ioo (-1 : ℝ) (-η) then
      Real.exp (-(q * (p.2.1 : ℝ))) *
      (if Y (p.2.1, p.1) ∈ Icc (u + δ) v then
        deriv w (Y (p.2.1, p.1)) * p.2.2 else 0) else 0
  obtain ⟨κ, hκfinite, hκeq⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  letI : IsSFiniteKernel κ := hκfinite
  have h66 :=
    avram_pj_reward66_original_stopped_firstorder_clock_joint_kernel_meas
      X hX hBV hSigmaZero q hq w C hC hCfinite hw0 hw_cont
      hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
      hjump n hn τ hτeq hτmeas hτstop ρ hρstop hρle
      G hGdef hGI A hA Cband u v δ η
      hu hδ hδ1 huv hη hη1 hv hvC hwCb
  have hLift : Measurable
      (fun p : Ω × (ℝ≥0 × ℝ) => (p.2.2, (p.2.1, p.1))) :=
    (measurable_snd.comp measurable_snd).prodMk
      ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  have hF : StronglyMeasurable F := by
    simpa only [F, Function.comp_def] using (h66.comp_measurable hLift)
  have hInt : StronglyMeasurable
      (fun ω : Ω => ∫ p, F (ω,p) ∂κ ω) :=
    hF.integral_kernel_prod_right'
  have hAE := hInt.aestronglyMeasurable (μ := P)
  have hK : ∀ ω, κ ω = NX ω := hκeq
  simp_rw [hK] at hAE
  simpa only [F, NX, Y] using hAE
