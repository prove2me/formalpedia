-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_outer_cash_eq_iSup_bounded_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:58:23.612209+00:00
-- url     : https://prove2.me/submissions/533e6a39-0c99-49ab-b8b4-01a19eb1e57b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_cash_eq_iSup_min_integer_clocks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Monotone convergence of full original Stieltjes cash at
    an arbitrary pathwise finite random stopping clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ⨆ n : ℕ, (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩
          Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by
  let θ : ℕ → Ω → ℝ≥0 := fun n ω => min (τ ω) (((n + 1 : ℕ) : ℝ≥0))
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ n ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hθMeas (n : ℕ) : Measurable (fun ω => (θ n ω : ℝ)) := by
    have hEq : (fun ω => (θ n ω : ℝ)) =
        (fun ω => min (τ ω : ℝ) (((n + 1 : ℕ) : ℝ))) := by
      funext ω
      simp only [θ, NNReal.coe_min, NNReal.coe_natCast]
    rw [hEq]
    exact hτMeas.min measurable_const
  have hFm (n : ℕ) : Measurable (F n) := by
    simpa only [F] using
      (avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
        X x D hD q (fun ω => (θ n ω : ℝ)) (hθMeas n))
  have hFmono : Monotone F := by
    intro n m hnm ω
    apply MeasureTheory.lintegral_mono_set
    intro t ht
    have hnmNN : (((n + 1 : ℕ) : ℝ≥0)) ≤ (((m + 1 : ℕ) : ℝ≥0)) := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hθNN : θ n ω ≤ θ m ω := min_le_min_left (τ ω) hnmNN
    have hθReal : (θ n ω : ℝ) ≤ (θ m ω : ℝ) := by
      exact_mod_cast hθNN
    exact ⟨ht.1, (Set.mem_Iic.mp ht.2).trans hθReal⟩
  have hPoint (ω : Ω) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ⨆ n : ℕ, F n ω := by
    exact
      (avram_wave7_03_original_finite_random_clock_cash_eq_iSup_min_integer_clocks
        X x D hD ω (τ ω) q)
  calc
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
      (∫⁻ ω, ⨆ n, F n ω ∂P) := by
        apply lintegral_congr
        intro ω
        exact hPoint ω
    _ = ⨆ n, (∫⁻ ω, F n ω ∂P) := lintegral_iSup hFm hFmono
    _ = ⨆ n : ℕ, (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩
          Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by
        rfl
