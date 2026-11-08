-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_zero_masked_F_uniform_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:35:45.79551+00:00
-- url     : https://prove2.me/submissions/9cc60b2f-9eb4-450f-8836-1c019e3d9238

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_integrable_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual finite-cap right-payment reward stays uniformly integrable
after masking its original zero-clock observations by the initial candidate. -/
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
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
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
    (hFI : ∀ k, Integrable (F k) P) :
    UniformIntegrable (fun k ω => if σ k ω = 0 then w x else F k ω)
      (1 : ℝ≥0∞) P := by
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
  let H : ℕ → Ω → ℝ := fun k ω =>
    if σ k ω = 0 then w x else F k ω
  let T : Ω → ℝ := fun ω => |w x| + G ω
  have hG0 : ∀ ω, 0 ≤ G ω := by
    intro ω
    exact add_nonneg hB ENNReal.toReal_nonneg
  have hT0 : ∀ ω, 0 ≤ T ω := by
    intro ω
    exact add_nonneg (abs_nonneg _) (hG0 ω)
  have hTI : Integrable T P := (integrable_const (|w x|)).add hGI
  have hHT : ∀ k ω, |H k ω| ≤ T ω := by
    intro k ω
    by_cases hz : σ k ω = 0
    · have hh : |w x| ≤ |w x| + G ω :=
        le_add_of_nonneg_right (hG0 ω)
      simpa only [H, hz, ite_true, T] using hh
    · have hh : |F k ω| ≤ |w x| + G ω :=
        (hBound k ω).trans (le_add_of_nonneg_left (abs_nonneg (w x)))
      simpa only [H, hz, ite_false, T] using hh
  have hHmeas : ∀ k, AEStronglyMeasurable (H k) P := by
    intro k
    exact (avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
      (σ k) (hσstop k) (F k) (hFI k) (w x)).aestronglyMeasurable
  have hDom : ∀ k, (fun ω => ‖H k ω‖ₑ) ≤ᵐ[P] (fun ω => ‖T ω‖ₑ) := by
    intro k
    filter_upwards [] with ω
    have hr : ‖H k ω‖ ≤ ‖T ω‖ := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hT0 ω)] using hHT k ω
    have hn : ‖H k ω‖₊ ≤ ‖T ω‖₊ :=
      (NNReal.coe_le_coe).mp (by simpa only [coe_nnnorm] using hr)
    simpa only [enorm_eq_nnnorm] using (ENNReal.coe_le_coe.mpr hn)
  let Tm : Ω → ℝ :=
    AEStronglyMeasurable.mk T hTI.aestronglyMeasurable
  have hTmStrong : StronglyMeasurable Tm :=
    hTI.aestronglyMeasurable.stronglyMeasurable_mk
  have hTeq : T =ᵐ[P] Tm := hTI.aestronglyMeasurable.ae_eq_mk
  have hTmMem : MemLp Tm (1 : ℝ≥0∞) P :=
    (memLp_congr_ae hTeq).mp (memLp_one_iff_integrable.mpr hTI)
  have hDomM : ∀ k, (fun ω => ‖H k ω‖ₑ) ≤ᵐ[P]
      (fun ω => ‖Tm ω‖ₑ) := by
    intro k
    filter_upwards [hDom k, hTeq] with ω hω heq
    simpa only [← heq] using hω
  change UniformIntegrable H (1 : ℝ≥0∞) P
  apply uniformIntegrable_of (by norm_num) (by norm_num) hHmeas
  intro ε hε
  obtain ⟨M, hMtail⟩ :=
    hTmMem.eLpNorm_indicator_norm_ge_le hTmStrong hε
  let K : ℝ≥0 := ⟨max 0 M, le_max_left 0 M⟩
  refine ⟨K, ?_⟩
  intro k
  have hTailDom : ∀ᵐ ω ∂P,
      ‖({ω : Ω | K ≤ ‖H k ω‖₊}.indicator (H k)) ω‖ₑ ≤
        ‖({ω : Ω | M ≤ (‖Tm ω‖₊ : ℝ)}.indicator Tm) ω‖ₑ := by
    filter_upwards [hDomM k] with ω hω
    by_cases hA : K ≤ ‖H k ω‖₊
    · have hn : ‖H k ω‖₊ ≤ ‖Tm ω‖₊ := by
        apply (ENNReal.coe_le_coe).mp
        simpa only [enorm_eq_nnnorm] using hω
      have hB : M ≤ (‖Tm ω‖₊ : ℝ) := by
        calc
          M ≤ max 0 M := le_max_right 0 M
          _ ≤ (‖Tm ω‖₊ : ℝ) := by exact_mod_cast (hA.trans hn)
      have hAmem : ω ∈ {u : Ω | K ≤ ‖H k u‖₊} := hA
      have hBmem : ω ∈ {u : Ω | M ≤ (‖Tm u‖₊ : ℝ)} := hB
      simpa only [Set.indicator_of_mem hAmem,
        Set.indicator_of_mem hBmem] using hω
    · have hAnot : ω ∉ {u : Ω | K ≤ ‖H k u‖₊} := hA
      simp only [Set.indicator_of_notMem hAnot, enorm_zero]
      exact bot_le
  exact (eLpNorm_mono_enorm_ae hTailDom).trans hMtail
