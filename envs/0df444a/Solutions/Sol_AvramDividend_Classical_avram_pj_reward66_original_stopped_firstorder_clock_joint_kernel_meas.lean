-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward66_original_stopped_firstorder_clock_joint_kernel_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:45:35.81319+00:00
-- url     : https://prove2.me/submissions/8068d62f-039f-4bd4-a6e0-92643c036ec0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_interior_deriv_zero_extension
set_option pp.universes true

set_option pp.explicit true
set_option pp.fullNames true
open MeasureTheory Set Filter Topology AvramDividend.Classical
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
      StronglyMeasurable (fun p : ℝ × (ℝ≥0 × Ω) =>
        if p.2.1 ≤ ρ p.2.2 ∧ p.1 ∈ Ioo (-1 : ℝ) (-η) then
          Real.exp (-(q * (p.2.1 : ℝ))) *
            (if Y (p.2.1, p.2.2) ∈ Icc (u + δ) v then
              deriv w (Y (p.2.1, p.2.2)) * p.1 else 0)
        else 0)) := by
  classical
  have hD0 : IsDividendStrategy 𝓕 D := hD.1.1
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun s => x + X.X s p.2 - rightLimit D s p.2) p.1
  have hY : Measurable Y := by
    exact avram_wave4_04b_controlled_postpayment_prejump_joint_measurable X x D hD0
  have hρM : Measurable (fun ω : Ω => (ρ ω : ℝ)) :=
    avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable ρ hρstop
  have hStop : MeasurableSet {p : ℝ≥0 × Ω | p.1 ≤ ρ p.2} := by
    have hm : MeasurableSet {p : ℝ≥0 × Ω |
        (p.1 : ℝ) ≤ (ρ p.2 : ℝ)} :=
      measurableSet_le (measurable_coe_nnreal_real.comp measurable_fst)
        (hρM.comp measurable_snd)
    convert hm using 1
    ext p
    simp
  let Z : Set ℝ := Ioo (-1 : ℝ) (-η)
  let g : ℝ → ℝ := fun y => if y ∈ Icc (u + δ) v then deriv w y else 0
  have hOpen := avram_wave4_04b_measurable_interior_deriv_zero_extension
    w (Ioo 0 Cband) isOpen_Ioo hwCb
  have hg : Measurable g := by
    have hz := hOpen.indicator (show MeasurableSet (Icc (u + δ) v) from measurableSet_Icc)
    have heq : g = (Icc (u + δ) v).indicator
        (fun y => if y ∈ Ioo 0 Cband then deriv w y else 0) := by
      funext y
      by_cases hy : y ∈ Icc (u + δ) v
      · have hInt : y ∈ Ioo 0 Cband := by
          rcases hy with ⟨hlo,hhi⟩
          exact ⟨by linarith,by linarith⟩
        simp only [g, Set.indicator, if_pos hy, if_pos hInt]
      · simp only [g, Set.indicator, if_neg hy]
    rw [heq]
    convert hz using 1
    funext y
    by_cases h : y ∈ Ioo 0 Cband
    · simp [h, Set.indicator]
    · simp [h, Set.indicator]
  have hZ : MeasurableSet Z := measurableSet_Ioo
  have hmask : MeasurableSet {p : ℝ × (ℝ≥0 × Ω) |
      p.2.1 ≤ ρ p.2.2 ∧ p.1 ∈ Z} := by
    exact (hStop.preimage measurable_snd).inter
      (hZ.preimage measurable_fst)
  have hMain : Measurable (fun p : ℝ × (ℝ≥0 × Ω) =>
      Real.exp (-(q * (p.2.1 : ℝ))) * (g (Y p.2) * p.1)) := by
    have hmY : Measurable (fun p : ℝ × (ℝ≥0 × Ω) => g (Y p.2)) :=
      hg.comp (hY.comp measurable_snd)
    have hmT : Measurable (fun p : ℝ × (ℝ≥0 × Ω) =>
        (p.2.1 : ℝ)) :=
      measurable_coe_nnreal_real.comp (measurable_fst.comp measurable_snd)
    exact (Real.measurable_exp.comp
      (measurable_const.mul hmT).neg).mul
      (hmY.mul measurable_fst)
  have hResult : StronglyMeasurable (fun p : ℝ × (ℝ≥0 × Ω) =>
      if p.2.1 ≤ ρ p.2.2 ∧ p.1 ∈ Z then
        Real.exp (-(q * (p.2.1 : ℝ))) * (g (Y p.2) * p.1) else 0) :=
    (hMain.ite hmask measurable_const).stronglyMeasurable
  simpa [g, Y, Z, ite_mul] using hResult
