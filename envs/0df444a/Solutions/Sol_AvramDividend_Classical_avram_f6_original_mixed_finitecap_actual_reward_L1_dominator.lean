-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_mixed_finitecap_actual_reward_L1_dominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:09:43.030316+00:00
-- url     : https://prove2.me/submissions/7207d62d-f5fe-48c0-948d-b3e422ca1c00

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_finitecap_true_caplinear_global_W_envelope
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_ruinbranch_W_le_runningSup
import Theorems.Thm_AvramDividend_Classical_avram_f6_mixed_gaussian_true_fixed_horizon_runningSup_L1
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_subclock_real_cash_dominated_if_full_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hwneg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (K : ℝ) (hK : ∀ y : ℝ, 0 ≤ y → y ≤ C.toReal → |w y| ≤ K)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτT : ∀ ω, τ ω ≤ T)
    (ρ : ℕ → Ω → ℝ≥0) (hρτ : ∀ m ω, ρ m ω ≤ τ ω)
    (Full : Ω → ℝ)
    (hFull : ∀ ω, Full ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal)
    (hFullI : Integrable Full P)
    (Approx : ℕ → Ω → ℝ)
    (hApprox : ∀ m ω, Approx m ω =
      Real.exp (-(q * (ρ m ω : ℝ))) *
        (let z : ℝ :=
           if ρ m ω = 0 ∨ (ρ m ω : ℝ≥0∞) < ruinTime X x D ω
           then x + X.X (ρ m ω) ω - rightLimit D (ρ m ω) ω
           else riskProcess X x D (ρ m ω) ω
         if ENNReal.ofReal z ≤ C then w z
         else w C.toReal + (z - C.toReal)) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ m ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) :
    ∃ B : Ω → ℝ, Integrable B P ∧
      ∀ m ω, |Approx m ω| ≤ B ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  let B : Ω → ℝ := fun ω => K + x + runningSup X T ω + Full ω
  have hsupI := avram_f6_mixed_gaussian_true_fixed_horizon_runningSup_L1 X hσ T
  have hBI : Integrable B P := by
    dsimp [B]
    exact ((integrable_const (K + x)).add hsupI).add hFullI
  refine ⟨B, hBI, ?_⟩
  intro m ω
  have hFinite : ∀ η : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D η) ∩ Iic (τ η : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D η)) ≠ ⊤ := by
    intro η
    rw [avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
      X x D hD η (τ η) q hq]
    exact ENNReal.ofReal_ne_top
  have hcash := avram_f6_original_subclock_real_cash_dominated_if_full_finite
    X x q D τ ρ hρτ hFinite m ω
  let W : ℝ := if ρ m ω = 0 ∨ (ρ m ω : ℝ≥0∞) < ruinTime X x D ω
    then x + X.X (ρ m ω) ω - rightLimit D (ρ m ω) ω
    else riskProcess X x D (ρ m ω) ω
  let V : ℝ := if ENNReal.ofReal W ≤ C then w W
    else w C.toReal + (W - C.toReal)
  let E : ℝ := Real.exp (-(q * (ρ m ω : ℝ)))
  let Cash : ℝ := (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
    Iic (ρ m ω : ℝ), ENNReal.ofReal (Real.exp (-(q * t)))
    ∂(dividendMeasure D ω)).toReal
  have hW : W ≤ x + runningSup X T ω :=
    avram_f6_original_true_ruinbranch_W_le_runningSup
      X x D hD T (ρ m ω) (le_trans (hρτ m ω) (hτT ω)) ω
  have hS : 0 ≤ x + runningSup X T ω := by
    have hs := (runningSup_eq_rawSup_nonneg X T ω).2
    linarith
  have hV : |V| ≤ K + x + runningSup X T ω := by
    simpa only [V, add_assoc] using
      (avram_f6_finitecap_true_caplinear_global_W_envelope
        w hwneg C hC K hK (x + runningSup X T ω) W hS hW)
  have hEpos : 0 ≤ E := (Real.exp_pos _).le
  have hEle : E ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have ht : 0 ≤ (ρ m ω : ℝ) := (ρ m ω).property
    nlinarith
  have hKnn : 0 ≤ K := by
    have hh := hK 0 le_rfl ENNReal.toReal_nonneg
    exact le_trans (abs_nonneg _) hh
  have hKS : 0 ≤ K + x + runningSup X T ω := by linarith
  have hmul : |E * V| ≤ K + x + runningSup X T ω := by
    rw [abs_mul, abs_of_nonneg hEpos]
    exact le_trans (mul_le_mul_of_nonneg_left hV hEpos)
      (mul_le_of_le_one_left hKS hEle)
  have hcash_bound : Cash ≤ Full ω := by
    rw [hFull ω]
    exact hcash
  have hC0 : 0 ≤ Cash := ENNReal.toReal_nonneg
  rw [hApprox m ω]
  change |E * V + Cash| ≤ B ω
  dsimp [B]
  calc
    _ ≤ |E * V| + |Cash| := abs_add_le _ _
    _ ≤ K + x + runningSup X T ω + Full ω := by
      rw [abs_of_nonneg hC0]
      exact add_le_add hmul hcash_bound
