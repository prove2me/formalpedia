-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin19_original_spatial_reward_eventwise_fatou_from_exact_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:57:21.430789+00:00
-- url     : https://prove2.me/submissions/1a362975-92bd-4a61-a8ce-526a19a3cfae

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_bounded_clock_cofinal_full_reward_eventually_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (σ : Ω → ℝ≥0)
    (hσbound : ∀ ω, (σ ω : ℝ≥0∞) ≤ (n : ℝ≥0∞))
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ᵐ ω ∂P, (⨆ k : ℕ, S k ω) = ⊤)
    (σk : ℕ → Ω → ℝ≥0)
    (hσk : ∀ k ω, σk k ω = (min (σ ω : ℝ≥0∞) (S k ω)).toNNReal)
    (F : Ω → ℝ) (Fk : ℕ → Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFksource : ∀ k ω, Fk k ω =
      Real.exp (-(q * (σk k ω : ℝ))) *
        w (if σk k ω = 0 ∨
              (σk k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σk k ω) ω - rightLimit D (σk k ω) ω
          else riskProcess X x D (σk k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hσmeas : Measurable σ)
    (hσkmeas : ∀ k, Measurable (σk k))
    (hσkle : ∀ k ω, σk k ω ≤ σ ω)
    (hFmeas : AEStronglyMeasurable F P)
    (hFkmeas : ∀ k, Measurable (Fk k))
    (hFkint : ∀ k, Integrable (Fk k) P)
    (hFpos : ∀ ω, σ ω ≠ 0 → 0 ≤ F ω)
    (hFkpos : ∀ k ω, σk k ω ≠ 0 → 0 ≤ Fk k ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (b : ℝ) (hb : 0 ≤ b)
    (hBudget : ∀ k,
      (∫ ω in A ∩ {η : Ω | σk k η ≠ 0}, Fk k ω ∂P) ≤ b) :
    (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, F ω ∂P) ≤ b := by
  classical
  have hEvent :
      ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
        σk k ω = σ ω ∧ Fk k ω = F ω :=
    avram_mix_fin18_original_bounded_clock_cofinal_full_reward_eventually_exact
      X x q w D n σ hσbound S hSmono hSsup σk hσk
      F Fk hFsource hFksource
  let E : (Ω → ℝ≥0) → Set Ω :=
    fun ζ => A ∩ {ω : Ω | ζ ω ≠ 0}
  have hEmeas (ζ : Ω → ℝ≥0) (hζ : Measurable ζ) :
      MeasurableSet (E ζ) := by
    have hz : MeasurableSet {ω : Ω | ζ ω = 0} := hζ (measurableSet_singleton (0 : ℝ≥0))
    have hnz : MeasurableSet {ω : Ω | ζ ω ≠ 0} := by
      simpa only [Set.compl_setOf] using hz.compl
    exact hA.inter hnz
  let Gk : ℕ → Ω → ℝ :=
    fun k ω => if ω ∈ E (σk k) then Fk k ω else 0
  let G : Ω → ℝ := fun ω => if ω ∈ E σ then F ω else 0
  have hGk_eq (k : ℕ) : Gk k = (E (σk k)).indicator (Fk k) :=
    funext (fun ω => by simp [Gk, Set.indicator])
  have hG_eq : G = (E σ).indicator F :=
    funext (fun ω => by simp [G, Set.indicator])
  have hGkm (k : ℕ) : Measurable (Gk k) :=
    Measurable.ite (hEmeas (σk k) (hσkmeas k)) (hFkmeas k) measurable_const
  have hGki (k : ℕ) : Integrable (Gk k) P := by
    rw [hGk_eq k]; exact (hFkint k).indicator (hEmeas (σk k) (hσkmeas k))
  have hGkpos (k : ℕ) : 0 ≤ᵐ[P] Gk k := by
    change ∀ᵐ ω ∂P, (0 : ℝ) ≤ Gk k ω
    filter_upwards [] with ω
    by_cases he : ω ∈ E (σk k)
    · simpa [Gk, he] using hFkpos k ω he.2
    · simp [Gk, he]
  have hGm : AEStronglyMeasurable G P := by
    rw [hG_eq]; exact hFmeas.indicator (hEmeas σ hσmeas)
  have hGpos : 0 ≤ᵐ[P] G := by
    change ∀ᵐ ω ∂P, (0 : ℝ) ≤ G ω
    filter_upwards [] with ω
    by_cases he : ω ∈ E σ
    · simpa [G, he] using hFpos ω he.2
    · simp [G, he]
  have hGbudget (k : ℕ) : (∫ ω, Gk k ω ∂P) ≤ b := by
    rw [hGk_eq k, integral_indicator (hEmeas (σk k) (hσkmeas k))]
    simpa only [E] using hBudget k
  have hGlim :
      ∀ᵐ ω ∂P, Tendsto (fun k => ENNReal.ofReal (Gk k ω)) atTop
        (𝓝 (ENNReal.ofReal (G ω))) := by
    filter_upwards [hEvent] with ω hω
    obtain ⟨K, hK⟩ := hω
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop K] with k hk
    have hEv : ω ∈ E (σk k) ↔ ω ∈ E σ := by
      simp [E, (hK k hk).1]
    have hVal : Gk k ω = G ω := by
      dsimp [Gk, G]
      rw [(hK k hk).2]
      by_cases he : ω ∈ E σ
      · simp [he, hEv.mpr he]
      · have hkNo : ω ∉ E (σk k) := fun hx => he (hEv.mp hx)
        simp [he, hkNo]
    exact congrArg ENNReal.ofReal hVal.symm
  have hB (k : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (Gk k ω) ∂P) ≤ ENNReal.ofReal b := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hGki k) (hGkpos k)]
    exact (ENNReal.ofReal_le_ofReal_iff hb).mpr (hGbudget k)
  have hLin :
      (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) ≤ ENNReal.ofReal b := by
    calc
      (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) =
          (∫⁻ ω, Filter.liminf
            (fun k => ENNReal.ofReal (Gk k ω)) atTop ∂P) := by
          apply lintegral_congr_ae
          filter_upwards [hGlim] with ω h
          exact (h.liminf_eq).symm
      _ ≤ Filter.liminf
          (fun k => ∫⁻ ω, ENNReal.ofReal (Gk k ω) ∂P) atTop :=
            lintegral_liminf_le (fun k => (hGkm k).ennreal_ofReal)
      _ ≤ ENNReal.ofReal b := by
          apply Filter.liminf_le_of_le
          · change Filter.IsBoundedUnder
                (fun x y : ℝ≥0∞ => x ≥ y) atTop
                (fun k => ∫⁻ ω, ENNReal.ofReal (Gk k ω) ∂P)
            exact ⟨0, Filter.Eventually.of_forall (fun k => bot_le)⟩
          · intro c hc
            obtain ⟨k, hck, hbk⟩ :=
              (hc.and (Filter.Eventually.of_forall hB)).exists
            exact hck.trans hbk
  have hGI : Integrable G P :=
    (lintegral_ofReal_ne_top_iff_integrable hGm hGpos).mp
      (ne_of_lt (lt_of_le_of_lt hLin ENNReal.ofReal_lt_top))
  have hEq : ENNReal.ofReal (∫ ω, G ω ∂P) =
      (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) :=
    ofReal_integral_eq_lintegral_ofReal hGI hGpos
  have hResult : (∫ ω, G ω ∂P) ≤ b := (ENNReal.ofReal_le_ofReal_iff hb).mp (hEq.trans_le hLin)
  rw [hG_eq, integral_indicator (hEmeas σ hσmeas)] at hResult
  exact hResult
