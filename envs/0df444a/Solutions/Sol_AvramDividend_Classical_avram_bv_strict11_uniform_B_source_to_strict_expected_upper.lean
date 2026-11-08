-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict11_uniform_B_source_to_strict_expected_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:05:45.045844+00:00
-- url     : https://prove2.me/submissions/db4a176d-1e18-4901-bf55-2bcd9e65507a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uniform_strict_delta_antitone_vanishes
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
import Theorems.Thm_AvramDividend_Classical_avram_redux9_original_uniform_grid_total_B_ae_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict11_two_error_physical_cofinal_strict_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original prescribed uniform BV generator source and two-scale stopped
    martingale certificate imply the strict real expected payout budget. -/
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
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (B : ℕ → Ω → ℝ)
    (hB : ∀ n ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      B n ω =
        (∑ i ∈ Finset.range (n + 1),
          if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u n (i + 1) : ℝ) - (u n i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
           ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
           else 0) * (R (u n i) - R (u n (i + 1)))))
    (hSource :
      let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
      let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
      let F : ℕ → Ω → ℝ := fun n ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)
      ∃ (M ErrCell ErrContact : ℕ → ℕ → Ω → ℝ) (η : ℕ → ℝ),
        (∀ n, 0 < η n) ∧
        Tendsto η atTop (nhds (0 : ℝ)) ∧
        (∀ n k, Integrable (M n k) P ∧
          (∫ ω, M n k ω ∂P) = 0) ∧
        (∀ n k, Integrable (fun ω => max (ErrCell n k ω) 0) P) ∧
        (∀ n k, Integrable (fun ω => max (ErrContact n k ω) 0) P) ∧
        (∀ n k, ∀ᵐ ω ∂P,
          F n ω ≤ w x + (M n k ω + B n ω) +
            max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0) ∧
        (∀ n (ε : ℝ), 0 < ε →
          ∃ k : ℕ,
            (∫ ω, max (ErrCell n k ω) 0 ∂P) +
              (∫ ω, max (ErrContact n k ω) 0 ∂P) ≤ η n + ε)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    (∫ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
  obtain ⟨M, ErrCell, ErrContact, η, hηpos, hηzero,
    hM, hCell, hContact, hBudget, hApprox⟩ := hSource
  obtain ⟨hδpairs, hδAnti, hδZero⟩ :=
    avram_p3_grid4_uniform_strict_delta_antitone_vanishes T hT
  have hCutMon : Monotone (fun n : ℕ => T - δ n) := by
    intro i j hij
    exact sub_le_sub_left (hδAnti hij) T
  have hCut0 (n : ℕ) : 0 ≤ T - δ n :=
    sub_nonneg.mpr (hδpairs n).2
  have hCutBelow (n : ℕ) : T - δ n ≤ (S : ℝ) := by
    change T - δ n ≤ T
    exact sub_le_self T (le_of_lt (hδpairs n).1)
  have hCutT :
      Tendsto (fun n : ℕ => T - δ n) atTop (nhds T) :=
    (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hT).2
  have hCutCover (s : ℝ) (hs : s < (S : ℝ)) :
      ∃ n : ℕ, s < T - δ n := by
    have h : ∀ᶠ n in atTop, s < T - δ n := by
      apply hCutT.eventually
      exact isOpen_Ioi.mem_nhds hs
    exact h.exists
  have hBforall :=
    avram_redux9_original_uniform_grid_total_B_ae_nonpositive
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hT u hgrid hmono huniform B hB
  have hBae (n : ℕ) : ∀ᵐ ω ∂P, B n ω ≤ 0 := by
    filter_upwards [hBforall] with ω hω
    exact hω n
  exact avram_bv_strict11_two_error_physical_cofinal_strict_mean
    X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) S
    (fun n => T - δ n) hCutMon hCut0 hCutBelow hCutCover
    F B (by intro n ω; rfl) M ErrCell ErrContact η
    hηpos hηzero hM hCell hContact hBae hBudget hApprox
