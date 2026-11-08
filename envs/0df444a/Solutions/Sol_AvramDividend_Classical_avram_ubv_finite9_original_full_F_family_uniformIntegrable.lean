-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_full_F_family_uniformIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:25:40.460882+00:00
-- url     : https://prove2.me/submissions/0f7ef525-8902-43e7-8db5-dae04a16f77d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_integrable_envelope
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original finite-cap full stopped value plus closed cash is uniformly integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hCashτI : Integrable
      (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFmeas : ∀ k, AEStronglyMeasurable (F k) P) :
    UniformIntegrable F (1 : ℝ≥0∞) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨B, hB, hBound, hGI⟩ :=
    avram_ubv_finite9_original_F_family_integrable_envelope
      X x q hq C hfinite hxc w hw_cont hw_neg D hD
      τ hCashτI σ hσle F hFsource
  let G : Ω → ℝ := fun ω =>
    B + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal
  have hG0 : ∀ ω, 0 ≤ G ω := by
    intro ω
    exact add_nonneg hB ENNReal.toReal_nonneg
  have hDom : ∀ k, (fun ω => ‖F k ω‖ₑ) ≤ᵐ[P] (fun ω => ‖G ω‖ₑ) := by
    intro k
    filter_upwards [] with ω
    have hR : ‖F k ω‖ ≤ ‖G ω‖ := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hG0 ω), G] using hBound k ω
    have hNN : ‖F k ω‖₊ ≤ ‖G ω‖₊ :=
      (NNReal.coe_le_coe).mp (by simpa only [coe_nnnorm] using hR)
    simpa only [enorm_eq_nnnorm] using (ENNReal.coe_le_coe.mpr hNN)
  let Gm : Ω → ℝ := AEStronglyMeasurable.mk G hGI.aestronglyMeasurable
  have hGmStrong : StronglyMeasurable Gm :=
    hGI.aestronglyMeasurable.stronglyMeasurable_mk
  have hGeq : G =ᵐ[P] Gm := hGI.aestronglyMeasurable.ae_eq_mk
  have hGmMem : MemLp Gm (1 : ℝ≥0∞) P :=
    (memLp_congr_ae hGeq).mp (memLp_one_iff_integrable.mpr hGI)
  have hDomM : ∀ k, (fun ω => ‖F k ω‖ₑ) ≤ᵐ[P] (fun ω => ‖Gm ω‖ₑ) := by
    intro k
    filter_upwards [hDom k, hGeq] with ω hω heq
    simpa only [← heq] using hω
  apply uniformIntegrable_of (by norm_num) (by norm_num) hFmeas
  intro ε hε
  obtain ⟨M, hMtail⟩ :=
    hGmMem.eLpNorm_indicator_norm_ge_le hGmStrong hε
  let K : ℝ≥0 := ⟨max 0 M, le_max_left 0 M⟩
  refine ⟨K, ?_⟩
  intro k
  have hTailDom : ∀ᵐ ω ∂P,
      ‖({ω : Ω | K ≤ ‖F k ω‖₊}.indicator (F k)) ω‖ₑ ≤
        ‖({ω : Ω | M ≤ (‖Gm ω‖₊ : ℝ)}.indicator Gm) ω‖ₑ := by
    filter_upwards [hDomM k] with ω hω
    by_cases hA : K ≤ ‖F k ω‖₊
    · have hNN : ‖F k ω‖₊ ≤ ‖Gm ω‖₊ := by
        apply (ENNReal.coe_le_coe).mp
        simpa only [enorm_eq_nnnorm] using hω
      have hB : M ≤ (‖Gm ω‖₊ : ℝ) := by
        calc
          M ≤ max 0 M := le_max_right 0 M
          _ ≤ (‖Gm ω‖₊ : ℝ) := by exact_mod_cast (hA.trans hNN)
      have hAmem : ω ∈ {u : Ω | K ≤ ‖F k u‖₊} := hA
      have hBmem : ω ∈ {u : Ω | M ≤ (‖Gm u‖₊ : ℝ)} := hB
      simpa only [Set.indicator_of_mem hAmem, Set.indicator_of_mem hBmem] using hω
    · have hAnot : ω ∉ {u : Ω | K ≤ ‖F k u‖₊} := hA
      simp only [Set.indicator_of_notMem hAnot, enorm_zero]
      exact bot_le
  exact (eLpNorm_mono_enorm_ae hTailDom).trans hMtail
