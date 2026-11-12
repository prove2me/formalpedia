-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger128_original_positive_clock_fixed_mesh_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:39:18.078802+00:00
-- url     : https://prove2.me/submissions/b4c783d2-ae93-4c55-b97a-8b4bc960b680

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger132_original_stopped_uniform_mesh_interior_cash_contact_budget
import Theorems.Thm_AvramDividend_Classical_avram_gledger133_original_stopped_mesh_terminal_contact_and_tail
import Theorems.Thm_AvramDividend_Classical_avram_gledger134_original_positive_clock_uniform_mesh_cash_partition
import Theorems.Thm_AvramDividend_Classical_avram_gledger117_original_initial_contact_plus_dividend_atom_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
import Theorems.Thm_AvramDividend_Classical_avram_gledger101_contact_cash_finite_algebra
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (n : ℕ) (ρ : ℝ≥0)
    (hρpos : 0 < ρ) (hρn : ρ ≤ (n : ℝ≥0))
    (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω)
    (j : ℕ)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1))
    (m : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℕ → ℝ := fun i => x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let F : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    let B : ℝ :=
      let δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let T : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ : ℝ) - δ) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      q * δ * Real.exp (q * (n : ℝ)) * F + T
    max ((w (x - rightLimit D 0 ω) - w x) +
      Finset.sum (Finset.range (m + 2)) (fun i => E (v (i + 1)) *
        ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
         (w (Y (i + 1)) - w (riskProcess X x D (v (i + 1)) ω)))) +
      E ρ * (w (riskProcess X x D ρ ω) -
        w (x + X.X ρ ω - rightLimit D ρ ω)) + F) 0 ≤ B := by
  dsimp only
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let A : ℕ → ℝ := fun i => E (v (i + 1)) *
    (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
     w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω))
  let F : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
    ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let U : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
    Ioo ((ρ : ℝ) - (Δ : ℝ)) (ρ : ℝ),
    ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let R : ℝ := q * (Δ : ℝ) * Real.exp (q * (n : ℝ)) * F
  let z : ℝ := w (x - rightLimit D 0 ω) - w x
  let cash0 : ℝ := ((dividendMeasure D ω) ({0} : Set ℝ)).toReal
  let term : ℝ := E ρ * (w (riskProcess X x D ρ ω) -
    w (x + X.X ρ ω - rightLimit D ρ ω))
  obtain ⟨k, hk, hvk, hstop, hinterior, htail, hpre0⟩ :=
    avram_gledger132_original_stopped_uniform_mesh_interior_cash_contact_budget
      X x D hD.1.1 ω q (le_of_lt hq) w C hTopCap hw0 hw_cont
      hw_neg hw_grad n m ρ hρpos hρn hρruin
      ((1 : ℝ) / ((j : ℝ) + 1)) (by positivity)
      (fun t ht htr => (hprefix t ht htr).1)
  let I : ℝ := ∑ i ∈ Finset.range k,
    (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  have hpre : (∑ i ∈ Finset.range k, A i) + I ≤ R := by simpa only [A, E, I, R, F, v, Δ] using hpre0
  obtain ⟨hlast0, hafter0⟩ :=
    avram_gledger133_original_stopped_mesh_terminal_contact_and_tail
      X x D hD.1.1 ω ρ v k hvk hstop htail w C hTopCap hw0
      hw_cont hw_neg hw_grad q
  have hlast : A k + term ≤ 0 := by simpa only [A, E, term, v] using hlast0
  have hafter : ∀ i : ℕ, k < i → A i = 0 := by intro i hi; simpa only [A, E, v] using hafter0 i hi
  have hcash : F ≤ cash0 + I + U := by
    simpa only [F, cash0, I, U, v, Δ] using
      (avram_gledger134_original_positive_clock_uniform_mesh_cash_partition
        X x C D hD ω q (le_of_lt hq) n m ρ hρn hρruin k
        hvk hstop hinterior)
  have hRight := (avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
    X x D hD.1.1 w hjump ω).2.2
  have hzero : z + cash0 ≤ 0 := by
    simpa only [z, cash0] using
      (avram_gledger117_original_initial_contact_plus_dividend_atom_nonpositive
        X w x C D hD hjump ω (hD.1.1.1 ω) hRight)
  have herr : 0 ≤ R + U := by dsimp [R, U]; positivity
  have hresult := avram_gledger101_contact_cash_finite_algebra
    A (m + 2) k hk hafter I U R F z cash0 term hpre hlast hzero hcash herr
  have hsum : (∑ i ∈ Finset.range (m + 2), E (v (i + 1)) *
      ((w (riskProcess X x D (v (i + 1)) ω) -
        w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)) +
       (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
        w (riskProcess X x D (v (i + 1)) ω)))) =
      ∑ i ∈ Finset.range (m + 2), A i := by
    apply Finset.sum_congr rfl
    intro i hi; dsimp [A]; ring
  rw [hsum]
  simpa only [A, E, R, U, F, z, term, v, Δ, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat] using hresult
