-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva41_all_activity_physical_prefix_expected_budget_nonL1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:56:39.050196+00:00
-- url     : https://prove2.me/submissions/cbc48232-291c-40ba-863b-46be17ffd891
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_uniform_grid_exists_exact_B_nonpositive_and_true_prepayment
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_original_physical_nonintegrable_error_witness
import Theorems.Thm_AvramDividend_Classical_avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bvb60_original_all_BV_strict_cash_full_T_expected_monotone
import Theorems.Thm_AvramDividend_Classical_avram_bva37_monotone_nonintegrable_signed_B_error_transfer
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, (∫ ω, F n ω ∂P) ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  let u : ℕ → ℕ → ℝ≥0 := fun k i =>
    ⟨T * (i : ℝ) / ((k : ℝ) + 2), by positivity⟩
  have huniform : ∀ k i, (u k i : ℝ) =
      T * (i : ℝ) / ((k : ℝ) + 2) := by
    intro k i
    rfl
  have hu : ∀ k i, u k i ≤ u k (i + 1) := by
    intro k i
    change T * (i : ℝ) / ((k : ℝ) + 2) ≤
      T * ((i + 1 : ℕ) : ℝ) / ((k : ℝ) + 2)
    gcongr
    exact_mod_cast Nat.le_succ i
  have hmono : ∀ k i, i < k + 1 → u k i ≤ u k (i + 1) := by
    intro k i _
    exact hu k i
  have hgrid : ∀ k, u k 0 = 0 ∧
      ((u k (k + 1) : ℝ) = T - T / ((k : ℝ) + 2)) := by
    intro k
    constructor
    · apply Subtype.ext
      simp [u]
    · change T * ((k + 1 : ℕ) : ℝ) / ((k : ℝ) + 2) =
        T - T / ((k : ℝ) + 2)
      push_cast
      have hk : (k : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring
  obtain ⟨B, hBexact, hBnonposAll, _⟩ :=
    avram_bvb_original_uniform_grid_exists_exact_B_nonpositive_and_true_prepayment
      X hX hBV q w C hw_gen x D hD.1.1 T hT u hu huniform
  obtain ⟨M, Err, hMI, hMeas, hEI, hErr, hBudget⟩ :=
    avram_a19_uniform_original_physical_nonintegrable_error_witness
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hT u hgrid hmono huniform B hBexact
  have hBnonpos : ∀ k, ∀ᵐ ω ∂P, B k ω ≤ 0 := by
    intro k
    filter_upwards [hBnonposAll] with ω hω
    exact hω k
  intro δ S F n
  have hFI : ∀ k, Integrable (F k) P := by
    simpa only [F, δ, S] using
      (avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
        X hBV x C D hD w hw_cont hw_neg q hq T hT)
  have hMono : ∀ k m, k ≤ m →
      (∫ ω, F k ω ∂P) ≤ (∫ ω, F m ω ∂P) := by
    simpa only [F, δ, S] using
      (avram_bvb60_original_all_BV_strict_cash_full_T_expected_monotone
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump T hT)
  have hBudget' : ∀ k, ∀ᵐ ω ∂P,
      F k ω ≤ w x + M k ω + B k ω + max (Err k ω) 0 := by
    intro k
    filter_upwards [hBudget k] with ω hω
    linarith
  exact (avram_bva37_monotone_nonintegrable_signed_B_error_transfer
    P F M B Err (w x) hFI hMono hMI hEI hBnonpos
    hBudget' hErr) n
