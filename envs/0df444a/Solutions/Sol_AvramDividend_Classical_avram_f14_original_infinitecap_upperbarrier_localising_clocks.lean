-- Prove2me | solution 1 for AvramDividend.Classical.avram_f14_original_infinitecap_upperbarrier_localising_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:38:25.055839+00:00
-- url     : https://prove2.me/submissions/ddee5d51-169d-4fb7-b5a8-41a8ae996287

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_toNNReal_clock_rightcont_stopping
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_literal_extended_bounds
import Theorems.Thm_AvramDividend_Classical_path_value_le_of_strict_prefix_le
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_record_grid_clocks_eventually_ge_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
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
    (hCashI : Integrable Cash P)
    (hCtop : C = ⊤) :
    ∃ σ : ℕ → Ω → ℝ≥0,
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (σ k ω : WithTop ℝ≥0))) ∧
      (∀ k, Measurable (fun ω => (σ k ω : ℝ))) ∧
      (∀ k ω, σ k ω ≤ τ ω) ∧
      (∀ k ω, X.X (σ k ω) ω ≤ (k : ℝ) + 1) ∧
      (∀ ω, ∀ᶠ k : ℕ in atTop, σ k ω = τ ω) := by
  classical
  let S : ℕ → Ω → ℝ≥0∞ :=
    fun k ω => twoSidedExitUpTime X ((k : ℝ) + 1) ω
  let σ : ℕ → Ω → ℝ≥0 :=
    fun k ω => (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal
  have hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k) := by
    intro k
    exact upperPassage_stopping_rightCont_filtration X ((k : ℝ) + 1)
  have hStop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)) := by
    exact avram_sweep16_original_double_min_toNNReal_clock_rightcont_stopping
      X x C D hD n S hSstop
  have hMeas : ∀ k, Measurable (fun ω => (σ k ω : ℝ)) := by
    apply avram_sweep16_original_double_min_clock_real_measurable
      X x C D hD n S hSstop σ
    intro k ω
    rfl
  have hCoee (k : ℕ) (ω : Ω) :
      (σ k ω : ℝ≥0∞) =
        min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω) := by
    exact (avram_sweep16_original_double_min_clock_literal_extended_bounds
      X x D n S k ω).1
  have hTauCoee (ω : Ω) :
      (τ ω : ℝ≥0∞) = min (ruinTime X x D ω) (n : ℝ≥0∞) := by
    rw [hτeq ω]
    have hle : min (ruinTime X x D ω) (n : ℝ≥0∞) ≤ (n : ℝ≥0∞) :=
      min_le_right _ _
    have hfinite : min (ruinTime X x D ω) (n : ℝ≥0∞) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) hle
    exact ENNReal.coe_toNNReal hfinite
  have hLe (k : ℕ) (ω : Ω) : σ k ω ≤ τ ω := by
    apply ENNReal.coe_le_coe.mp
    rw [hCoee, hTauCoee]
    exact min_le_left _ _
  have hBound (k : ℕ) (ω : Ω) :
      X.X (σ k ω) ω ≤ (k : ℝ) + 1 := by
    apply path_value_le_of_strict_prefix_le X ((k : ℝ) + 1)
      (by positivity) ω (σ k ω)
    intro t ht
    by_contra hfail
    have hbad : (k : ℝ) + 1 < X.X t ω := lt_of_not_ge hfail
    have hhitle : S k ω ≤ (t : ℝ≥0∞) := by
      dsimp [S, twoSidedExitUpTime]
      exact iInf_le_of_le t (iInf_le_of_le hbad le_rfl)
    have hclockle : (σ k ω : ℝ≥0∞) ≤ S k ω := by
      rw [hCoee]
      exact min_le_right _ _
    have htcoe : (t : ℝ≥0∞) < (σ k ω : ℝ≥0∞) :=
      ENNReal.coe_lt_coe.mpr ht
    exact (not_lt_of_ge (le_trans hclockle hhitle)) htcoe
  refine ⟨σ, hStop, hMeas, hLe, hBound, ?_⟩
  intro ω
  obtain ⟨N, hN⟩ :=
    firstUpcrossing_record_grid_clocks_eventually_ge_horizon X ω
      (n : ℝ≥0) 1 1 (by norm_num)
  filter_upwards [eventually_ge_atTop N] with k hk
  have hSge : (n : ℝ≥0∞) ≤ S k ω := by
    have h := hN k hk
    simpa [S, twoSidedExitUpTime, mul_one, add_comm] using h
  have hBaseLe : min (ruinTime X x D ω) (n : ℝ≥0∞) ≤ S k ω :=
    le_trans (min_le_right _ _) hSge
  apply ENNReal.coe_injective
  rw [hCoee, hTauCoee]
  exact min_eq_left hBaseLe
