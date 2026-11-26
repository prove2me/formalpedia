-- Prove2me | solution 4 for AvramDividend.Classical.avram_p4_f4_purejump_original_expected_reward_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T07:46:02.244955+00:00
-- url     : https://prove2.me/submissions/40e89f4d-7b45-4e0c-956d-9afeb98dd606
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_finite_barrier_exhaustion_preserves_exact_stopped_reward_data
import Theorems.Thm_AvramDividend_Classical_avram_jump6_finitecap_original_stopped_reward_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_purejump_finitecap_physical_HJB_mean
import Theorems.Thm_AvramDividend_Classical_avram_gfinite74_cap_gap_of_grad
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

private theorem finiteRewardBudget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P) (hFinite : C ≠ ⊤) :
    Integrable (fun ω => Term ω + Cash ω) P ∧
      (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by
  refine ⟨avram_jump6_finitecap_original_stopped_reward_integrable
    X x C hFinite hxc D hD q hq.le w hw_cont hw_neg n hn τ hτeq hτstop
    W Cash Term hW hCash hTerm, ?_⟩
  exact avram_p4_f4_purejump_finitecap_physical_HJB_mean
    X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop
    W Cash Term hW hCash hTerm hTermMeas hCashI hFinite

private theorem rewardBudgetByFiniteBarriers
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P) :
    Integrable (fun ω => Term ω + Cash ω) P ∧
      (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by
  classical
  by_cases hFinite : C ≠ ⊤
  · exact finiteRewardBudget X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
      hτstop W Cash Term hW hCash hTerm hTermMeas hCashI hFinite
  have hCtop : C = ⊤ := not_ne_iff.mp hFinite
  subst C
  let K : ℕ → ℝ := fun k => x + (k : ℝ) + 1
  let clk (L : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 :=
    (min (ruinTime X x L ω) (n : ℝ≥0∞)).toNNReal
  let termReserve (L : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
    if clk L ω = 0 ∨ (clk L ω : ℝ≥0∞) < ruinTime X x L ω then
      x + X.X (clk L ω) ω - rightLimit L (clk L ω) ω
    else riskProcess X x L (clk L ω) ω
  let paymentMeasure (L : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℝ :=
    (dividendMeasure L ω).restrict
      (paymentTimes (ruinTime X x L ω) ∩ Iic (clk L ω : ℝ))
  let F (L : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
    Real.exp (-(q * (clk L ω : ℝ))) * w (termReserve L ω) +
      (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂(paymentMeasure L ω)).toReal
  obtain ⟨E, hE, hEventually⟩ :=
    finite_barrier_exhaustion_preserves_exact_stopped_reward_data X x hx.le D hD.1 n
  have hSmoothTop : ContDiffOn ℝ 2 w (Ioi (0 : ℝ)) := by
    apply hw_smooth.mono
    intro y hy
    exact ⟨hy, ENNReal.ofReal_lt_top⟩
  have hGap (l u : ℝ) (hl : 0 ≤ l) (hlu : l ≤ u) : u - l ≤ w u - w l := by
    apply sub_nonneg.mp
    exact avram_gfinite74_cap_gap_of_grad w l u hlu
      (hw_cont.mono fun y hy => hl.trans hy.1)
      (fun y hy => (hSmoothTop.differentiableOn (by norm_num) y (hl.trans_lt hy.1)).differentiableAt
        (Ioi_mem_nhds (hl.trans_lt hy.1)))
      (fun y hy => hw_grad y (hl.trans_lt hy.1) (ENNReal.ofReal_lt_top))
  have hNonnegW (z : ℝ) : 0 ≤ w z := by
    by_cases hz : 0 ≤ z
    · linarith [hGap 0 z le_rfl hz]
    · rw [hw_neg z (lt_of_not_ge hz)]
  have hFNN (L : ℝ≥0 → Ω → ℝ) (ω : Ω) : 0 ≤ F L ω :=
    add_nonneg (mul_nonneg (Real.exp_pos _).le (hNonnegW _)) ENNReal.toReal_nonneg
  have hPerCap (k : ℕ) : Integrable (F (E k)) P ∧ (∫ ω, F (E k) ω ∂P) ≤ w x := by
    let B : ℝ≥0∞ := ENNReal.ofReal (K k)
    have hKpos : 0 < K k := by dsimp [K]; positivity
    have hB : 0 < B := ENNReal.ofReal_pos.mpr hKpos
    have hBK : B ≠ ⊤ := ENNReal.ofReal_ne_top
    have hxB : ENNReal.ofReal x ≤ B := by
      apply ENNReal.ofReal_le_ofReal
      dsimp [K]
      have hk : 0 ≤ (k : ℝ) := by positivity
      linarith
    have hAd : IsAdmissibleLe X x B (E k) := hE k
    have hjumpE (ω : Ω) (t : ℝ≥0)
        (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x (E k) ω) :
        rightLimit (E k) t ω - E k t ω ≤
          w (riskProcess X x (E k) t ω) -
            w (riskProcess X x (E k) t ω - (rightLimit (E k) t ω - E k t ω)) := by
      have h0 := sub_nonneg.mpr (hAd.1.2 ω t ht)
      have hδ := sub_nonneg.mpr (dividendStrategy_le_rightLimit (E k) hAd.1.1 ω t)
      linarith only [hGap _ _ h0 (sub_le_self _ hδ)]
    obtain ⟨τk, hτk, hτkMeas, hτkStop⟩ :=
      avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping X x (E k) n
        (ruinTime_measurable X x (E k) hAd.1.1)
        (ruinTime_stopping_rightCont_filtration X x (E k) hAd.1.1)
    obtain ⟨Wk, Cashk, Termk, hWk, hCashk, hTermk, hTermkMeas, hCashkI⟩ :=
      avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
        X x B (E k) hAd w hw_cont hw_neg q n τk hτk hτkMeas hτkStop
    have hEqual : (fun ω => Termk ω + Cashk ω) = F (E k) := by
      funext ω
      rw [hTermk ω, hWk ω, hCashk ω, hτk ω]
    rw [← hEqual]
    exact finiteRewardBudget X hX hBV hν hσ q hq w B hB hw0 hw_cont hw_neg
      (hw_smooth.mono fun y hy => ⟨hy.1, hy.2.trans_le le_top⟩)
      (fun y hy hyB => hw_gen y hy (hyB.trans_le le_top))
      (fun y hy hyB => hw_grad y hy (hyB.trans_le le_top))
      x hx hxB (E k) hAd (fun ω t _ _ => hNonnegW _) hjumpE
      n hn τk hτk hτkMeas hτkStop Wk Cashk Termk hWk hCashk hTermk hTermkMeas hCashkI hBK
  have hOrig : (fun ω => Term ω + Cash ω) = F D := by
    funext ω
    rw [hTerm ω, hW ω, hCash ω, hτeq ω]
  let H : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (F (E k) ω)
  have hHMeas (k : ℕ) : AEMeasurable (H k) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hPerCap k).1.aemeasurable
  have hLim (ω : Ω) : Tendsto (fun k => H k ω) atTop (𝓝 (ENNReal.ofReal (F D ω))) := by
    have hEq : (fun k => H k ω) =ᶠ[atTop] fun _ => ENNReal.ofReal (F D ω) := by
      filter_upwards [hEventually ω] with k hk
      have hk' : clk (E k) ω = clk D ω ∧ termReserve (E k) ω = termReserve D ω ∧
          paymentMeasure (E k) ω = paymentMeasure D ω := hk
      simp only [H, F, hk'.1, hk'.2.1, hk'.2.2]
    exact (tendsto_congr' hEq).mpr tendsto_const_nhds
  have hUniform (k : ℕ) : (∫⁻ ω, H k ω ∂P) ≤ ENNReal.ofReal (w x) := by
    change (∫⁻ ω, ENNReal.ofReal (F (E k) ω) ∂P) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal (hPerCap k).1 (Eventually.of_forall (hFNN (E k)))]
    exact ENNReal.ofReal_le_ofReal (hPerCap k).2
  have hBudget : (∫⁻ ω, ENNReal.ofReal (F D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
    calc
      _ = ∫⁻ ω, liminf (fun k => H k ω) atTop ∂P :=
        lintegral_congr_ae (Eventually.of_forall fun ω => (hLim ω).liminf_eq.symm)
      _ ≤ liminf (fun k => ∫⁻ ω, H k ω ∂P) atTop := lintegral_liminf_le' hHMeas
      _ ≤ _ := liminf_le_of_frequently_le (Eventually.of_forall hUniform).frequently
  have hOrigMeas : AEStronglyMeasurable (F D) P := by
    rw [← hOrig]
    exact hTermMeas.add hCashI.aestronglyMeasurable
  have hOrigNN : 0 ≤ᵐ[P] F D := Eventually.of_forall (hFNN D)
  have hI : Integrable (F D) P :=
    (lintegral_ofReal_ne_top_iff_integrable hOrigMeas hOrigNN).mp
      (ne_of_lt (hBudget.trans_lt ENNReal.ofReal_lt_top))
  rw [hOrig]
  refine ⟨hI, (ENNReal.ofReal_le_ofReal_iff (hNonnegW x)).mp ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hI hOrigNN]
  exact hBudget

set_option maxHeartbeats 800000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P) :
    Integrable (fun ω => Term ω + Cash ω) P ∧
      (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by
  exact rewardBudgetByFiniteBarriers
    X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop
    W Cash Term hW hCash hTerm hTermMeas hCashI
