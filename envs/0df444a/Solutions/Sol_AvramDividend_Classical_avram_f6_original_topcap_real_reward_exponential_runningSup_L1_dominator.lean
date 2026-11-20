-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_topcap_real_reward_exponential_runningSup_L1_dominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:42:40.758056+00:00
-- url     : https://prove2.me/submissions/b6e28bf7-2048-49e5-94a9-3971d51c5b30

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_exp_growth_scalar_value_envelope
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_ruinbranch_W_le_runningSup
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_subclock_real_cash_dominated_if_full_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hwneg : ∀ y < 0, w y = 0)
    (hwpos : ∀ y : ℝ, 0 ≤ y → 0 ≤ w y)
    (θ K : ℝ) (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hwGrowth : ∀ y, 0 ≤ y → w y ≤ K * Real.exp (θ * y))
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (ρ : ℕ → Ω → ℝ≥0) (hρτ : ∀ m ω, ρ m ω ≤ τ ω)
    (Full : Ω → ℝ)
    (hFull : ∀ ω, Full ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal)
    (hFullI : Integrable Full P)
    (hExpI : Integrable (fun ω => Real.exp (θ * runningSup X T ω)) P)
    (Approx : ℕ → Ω → ℝ)
    (hApprox : ∀ m ω, Approx m ω =
      Real.exp (-(q * (ρ m ω : ℝ))) *
        w (if ρ m ω = 0 ∨ (ρ m ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (ρ m ω) ω - rightLimit D (ρ m ω) ω
          else riskProcess X x D (ρ m ω) ω) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ m ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) :
    ∃ B : Ω → ℝ, Integrable B P ∧
      ∀ m ω, |Approx m ω| ≤ B ω := by
  let B : Ω → ℝ := fun ω =>
    K * Real.exp (θ * x) * Real.exp (θ * runningSup X T ω) + Full ω
  have hBI : Integrable B P := by
    change Integrable (fun ω =>
      (K * Real.exp (θ * x)) * Real.exp (θ * runningSup X T ω) + Full ω) P
    exact (hExpI.const_mul (K * Real.exp (θ * x))).add hFullI
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
  let E : ℝ := Real.exp (-(q * (ρ m ω : ℝ)))
  let Cash : ℝ := (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
    Iic (ρ m ω : ℝ), ENNReal.ofReal (Real.exp (-(q * t)))
    ∂(dividendMeasure D ω)).toReal
  have hW : W ≤ x + runningSup X T ω :=
    avram_f6_original_true_ruinbranch_W_le_runningSup X x D hD
      T (ρ m ω) (le_trans (hρτ m ω) (hτT ω)) ω
  have hV := avram_f6_original_topcap_exp_growth_scalar_value_envelope
    w hwneg hwpos θ K hθ hK hwGrowth (x + runningSup X T ω) W hW
  have hEpos : 0 ≤ E := (Real.exp_pos _).le
  have hEle : E ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have ht : 0 ≤ (ρ m ω : ℝ) := (ρ m ω).property
    nlinarith
  have hBoundpos : 0 ≤ K * Real.exp (θ * (x + runningSup X T ω)) :=
    mul_nonneg hK (Real.exp_pos _).le
  have hMul : |E * w W| ≤
      K * Real.exp (θ * (x + runningSup X T ω)) := by
    rw [abs_mul, abs_of_nonneg hEpos]
    exact le_trans (mul_le_mul_of_nonneg_left hV hEpos)
      (mul_le_of_le_one_left hBoundpos hEle)
  have hCash : Cash ≤ Full ω := by
    rw [hFull ω]
    exact hcash
  have hCashNonneg : 0 ≤ Cash := ENNReal.toReal_nonneg
  rw [hApprox m ω]
  change |E * w W + Cash| ≤ B ω
  dsimp [B]
  calc
    _ ≤ |E * w W| + |Cash| := abs_add_le _ _
    _ ≤ K * Real.exp (θ * (x + runningSup X T ω)) + Full ω := by
      rw [abs_of_nonneg hCashNonneg]
      exact add_le_add hMul hCash
    _ = K * Real.exp (θ * x) * Real.exp (θ * runningSup X T ω) +
        Full ω := by rw [mul_add, Real.exp_add]; ring
