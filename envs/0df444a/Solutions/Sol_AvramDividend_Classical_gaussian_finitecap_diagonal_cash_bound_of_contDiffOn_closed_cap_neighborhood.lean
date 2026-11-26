-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_finitecap_diagonal_cash_bound_of_contDiffOn_closed_cap_neighborhood
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T07:17:16.846798+00:00
-- url     : https://prove2.me/submissions/d22e3690-9d50-45fc-8534-f5fba357a7d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_gaussian_finitecap_stopped_ito_stieltjes_formula
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_positive_stop_terminal_prepayment_band
import Theorems.Thm_AvramDividend_Classical_avram_gfinite74_cap_gap_of_grad

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

set_option maxHeartbeats 800000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (hc : 0 < X.c)
    (q : ℝ) (hq : 0 < q) (v : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (a b : ℝ) (ha : a < 0) (hb : C.toReal < b)
    (hvSmooth : ContDiffOn ℝ 2 v (Ioo a b))
    (hvNonneg : ∀ y ∈ Icc (0 : ℝ) C.toReal, 0 ≤ v y)
    (hvGen : ∀ y ∈ Icc (0 : ℝ) C.toReal, X.generator v y - q * v y ≤ 0)
    (hvGrad : ∀ y ∈ Icc (0 : ℝ) C.toReal, 1 ≤ deriv v y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (v x) := by
  classical
  let ρ : Ω → ℝ≥0 := fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  let A : Ω → Set ℝ := fun ω =>
    paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ)
  let pre : ℝ≥0 → Ω → ℝ := riskProcess X x D
  let jump : ℝ≥0 → Ω → ℝ := fun t ω => rightLimit D t ω - D t ω
  let post : ℝ≥0 → Ω → ℝ := fun t ω => pre t ω - jump t ω
  let toll : Ω → ℝ → ℝ := fun ω s =>
    if jump s.toNNReal ω = 0 then deriv v (pre s.toNNReal ω)
    else (v (pre s.toNNReal ω) - v (post s.toNNReal ω)) / jump s.toNNReal ω
  let paid : Ω → ℝ → ℝ := fun ω s => Real.exp (-(q * s)) * toll ω s
  let finish : Ω → ℝ := fun ω =>
    if ρ ω = 0 then post (ρ ω) ω else pre (ρ ω) ω
  let driftTerm : Ω → ℝ → ℝ := fun ω s =>
    Real.exp (-(q * s)) * (X.generator v (pre s.toNNReal ω) - q * v (pre s.toNNReal ω))
  have hxCap : x ≤ C.toReal := by
    simpa only [ENNReal.toReal_ofReal hx.le] using ENNReal.toReal_mono hFinite hxc
  have ρ_le_ruin (ω : Ω) : (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω :=
    ENNReal.coe_toNNReal_le_self.trans (min_le_left _ _)
  have pre_in_band (ω : Ω) (t : ℝ≥0)
      (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
      pre t ω ∈ Icc (0 : ℝ) C.toReal := by
    rcases ht with hzero | hbefore
    · subst t
      simpa [pre, riskProcess, X.X_zero, hD.1.1.1 ω] using
        (show x ∈ Icc (0 : ℝ) C.toReal from ⟨hx.le, hxCap⟩)
    · obtain ⟨hNonneg, hUpper⟩ :=
        capped_riskProcess_range_before_ruin_including_zero X x hx.le C hxc D hD ω t hbefore
      exact ⟨hNonneg, by
        simpa only [pre, ENNReal.toReal_ofReal hNonneg] using ENNReal.toReal_mono hFinite hUpper⟩
  have jump_nonneg (ω : Ω) (t : ℝ≥0) : 0 ≤ jump t ω :=
    sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD.1.1 ω t)
  have post_in_band (ω : Ω) (t : ℝ≥0)
      (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
      post t ω ∈ Icc (0 : ℝ) C.toReal := by
    refine ⟨sub_nonneg.mpr (hD.1.2 ω t ht), ?_⟩
    exact (sub_le_self _ (jump_nonneg ω t)).trans (pre_in_band ω t ht).2
  have hInterior (z : ℝ) (hz : z ∈ Icc (0 : ℝ) C.toReal) : z ∈ Ioo a b :=
    ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩
  have hSecant (y z : ℝ) (hy : y ∈ Icc (0 : ℝ) C.toReal)
      (hz : z ∈ Icc (0 : ℝ) C.toReal) (hyz : y ≤ z) :
      z - y ≤ v z - v y := by
    apply sub_nonneg.mp
    exact avram_gfinite74_cap_gap_of_grad v y z hyz
      (hvSmooth.continuousOn.mono fun p hp =>
        hInterior p ⟨hy.1.trans hp.1, hp.2.trans hz.2⟩)
      (fun p hp =>
        let hp' := hInterior p ⟨hy.1.trans hp.1.le, hp.2.le.trans hz.2⟩
        (hvSmooth.differentiableOn (by norm_num) p hp').differentiableAt
          (Ioo_mem_nhds hp'.1 hp'.2))
      (fun p hp => hvGrad p ⟨hy.1.trans hp.1.le, hp.2.le.trans hz.2⟩)

  have hAMeas (ω : Ω) : MeasurableSet (A ω) :=
    (paymentTimes_measurable _).inter measurableSet_Iic
  have hToll (ω : Ω) (s : ℝ) (hs : s ∈ A ω) : 1 ≤ toll ω s := by
    have hsPay : 0 ≤ s ∧ (s = 0 ∨ ENNReal.ofReal s <
        min (ruinTime X x D ω) (n : ℝ≥0∞)) := hs.1
    have hsActive : s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω := by
      rcases hsPay.2 with hzero | hlt
      · left
        simp [hzero]
      · right
        rw [ENNReal.ofNNReal_toNNReal]
        exact hlt.trans_le (min_le_left _ _)
    have hPre := pre_in_band ω s.toNNReal hsActive
    have hPost := post_in_band ω s.toNNReal hsActive
    have hδ := jump_nonneg ω s.toNNReal
    have hsz : post s.toNNReal ω ≤ pre s.toNNReal ω := sub_le_self _ hδ
    dsimp only [toll]
    split_ifs with hzero
    · exact hvGrad _ hPre
    · apply (le_div_iff₀ (lt_of_le_of_ne hδ (Ne.symm hzero))).2
      rw [one_mul]
      have hdiff : pre s.toNNReal ω - post s.toNNReal ω = jump s.toNNReal ω := by
        dsimp only [post]
        ring
      simpa only [hdiff] using hSecant _ _ hPost hPre hsz

  have hTerminalBand : ∀ᵐ ω ∂P, 0 < ρ ω →
      0 ≤ pre (ρ ω) ω ∧ pre (ρ ω) ω ≤ C.toReal :=
    avram_gledger20_original_positive_stop_terminal_prepayment_band
      X hν x D hD.1.1 ρ 0 C.toReal
      (Filter.Eventually.of_forall fun ω t _ ht =>
        pre_in_band ω t (Or.inr ((ENNReal.coe_lt_coe.mpr ht).trans_le (ρ_le_ruin ω))))
  have hDriftNonpos (ω : Ω) : (∫ s in Ico (0 : ℝ) (ρ ω : ℝ), driftTerm ω s) ≤ 0 := by
    apply setIntegral_nonpos measurableSet_Ico
    intro s hs
    have hsCo : (s.toNNReal : ℝ) < (ρ ω : ℝ) := by
      simpa only [Real.coe_toNNReal s hs.1] using hs.2
    have hsNN : s.toNNReal < ρ ω := by exact_mod_cast hsCo
    have hBefore : (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω :=
      (ENNReal.coe_lt_coe.mpr hsNN).trans_le (ρ_le_ruin ω)
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (hvGen _ (pre_in_band ω s.toNNReal (Or.inr hBefore)))

  have hIto :
      ∃ M : Ω → ℝ, Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      ∀ᵐ ω ∂P, IntegrableOn (paid ω) (A ω) (dividendMeasure D ω) ∧
        (Real.exp (-(q * (ρ ω : ℝ))) * v (finish ω) +
            (∫ s in A ω, paid ω s ∂(dividendMeasure D ω)) =
          v x + M ω + (∫ s in Ico (0 : ℝ) (ρ ω : ℝ), driftTerm ω s)) :=
    gaussian_finitecap_stopped_ito_stieltjes_formula
      X hX hBV hν q hq v C hC hFinite a b ha hb hvSmooth x hx hxc D hD n hn
  obtain ⟨M, hMI, hM0, hIdentity⟩ := hIto
  have hPath : ∀ᵐ ω ∂P,
      (∫⁻ s in A ω, ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (v x + M ω) ∧ 0 ≤ v x + M ω := by
    filter_upwards [hTerminalBand, hIdentity] with ω hBand h
    have hFinishInBand : finish ω ∈ Icc (0 : ℝ) C.toReal := by
      dsimp only [finish]
      split_ifs with hzero
      · exact post_in_band ω (ρ ω) (Or.inl hzero)
      · have hpos : 0 < ρ ω := by
          apply lt_of_le_of_ne
          · positivity
          · intro hz
            exact hzero hz.symm
        exact hBand hpos
    have hTerminalNN : 0 ≤ Real.exp (-(q * (ρ ω : ℝ))) * v (finish ω) :=
      mul_nonneg (Real.exp_pos _).le (hvNonneg _ hFinishInBand)
    have hTollNN :
        0 ≤ᵐ[(dividendMeasure D ω).restrict (A ω)] paid ω :=
      (ae_restrict_mem (hAMeas ω)).mono fun s hs =>
        mul_nonneg (Real.exp_pos _).le ((by norm_num : (0 : ℝ) ≤ 1).trans (hToll ω s hs))
    have hTollIntegralNN : 0 ≤ ∫ s in A ω, paid ω s ∂(dividendMeasure D ω) :=
      integral_nonneg_of_ae hTollNN
    have hCashLe :
        (∫⁻ s in A ω, ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
          ENNReal.ofReal (∫ s in A ω, paid ω s ∂(dividendMeasure D ω)) := by
      calc
        _ ≤ ∫⁻ s in A ω, ENNReal.ofReal (paid ω s) ∂(dividendMeasure D ω) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem (hAMeas ω)] with s hs
          apply ENNReal.ofReal_le_ofReal
          change Real.exp (-(q * s)) ≤ Real.exp (-(q * s)) * toll ω s
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (hToll ω s hs) (Real.exp_pos _).le
        _ = _ := (ofReal_integral_eq_lintegral_ofReal h.1 hTollNN).symm
    have hTollLe : (∫ s in A ω, paid ω s ∂(dividendMeasure D ω)) ≤ v x + M ω := by
      linarith only [h.2, hTerminalNN, hDriftNonpos ω]
    exact ⟨hCashLe.trans (ENNReal.ofReal_le_ofReal hTollLe), hTollIntegralNN.trans hTollLe⟩

  letI : IsProbabilityMeasure P := X.isProbability
  have hSumI : Integrable (fun ω => v x + M ω) P := (integrable_const (v x)).add hMI
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (v x + M ω) ∂P :=
      lintegral_mono_ae (hPath.mono fun ω h => h.1)
    _ = ENNReal.ofReal (∫ ω, v x + M ω ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hSumI (hPath.mono fun ω h => h.2)).symm
    _ = ENNReal.ofReal (v x) := by
      rw [integral_add (integrable_const (v x)) hMI, hM0]
      simp
