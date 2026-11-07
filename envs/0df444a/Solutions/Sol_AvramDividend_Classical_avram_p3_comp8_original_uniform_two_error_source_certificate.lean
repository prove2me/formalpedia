-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_original_uniform_two_error_source_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:43:33.147196+00:00
-- url     : https://prove2.me/submissions/bf1d76d7-0275-4aa4-b86d-b097cf0e1ed3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_centred_positive_excess_without_B_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A vanishing positive source residual gives the two-error certificate,
    with all original physical grid source terms preserved. -/
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
    (hBI : ∀ n, Integrable (B n) P) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    ∃ M ErrCell ErrContact : ℕ → Ω → ℝ,
      (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (ErrCell n ω) 0) P) ∧
      (∀ n, Integrable (fun ω => max (ErrContact n ω) 0) P) ∧
      (∀ n, ∀ᵐ ω ∂P, F n ω ≤
        w x + (M n ω + B n ω) +
          max (ErrCell n ω) 0 + max (ErrContact n ω) 0) ∧
      Tendsto (fun n => ∫ ω, max (ErrCell n ω) 0 ∂P)
        atTop (nhds (0 : ℝ)) ∧
      Tendsto (fun n => ∫ ω, max (ErrContact n ω) 0 ∂P)
        atTop (nhds (0 : ℝ)) := by
  dsimp
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  obtain ⟨M, hMI, hEI, hEzero⟩ :=
    avram_a19_uniform_centred_positive_excess_without_B_L1
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hT u hgrid hmono huniform B hB
  letI : IsProbabilityMeasure P := X.isProbability
  refine ⟨M,
    (fun n ω => F n ω - (w x + (M n ω + B n ω))),
    (fun _ _ => 0), hMI, ?_, ?_, ?_, hEzero, ?_⟩
  · intro n
    exact hEI n
  · intro n
    simpa only [max_self] using
      (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) P)
  · intro n
    filter_upwards [] with ω
    change F n ω ≤ w x + (M n ω + B n ω) +
      max (F n ω - (w x + (M n ω + B n ω))) 0 + max (0 : ℝ) 0
    have hm : F n ω - (w x + (M n ω + B n ω)) ≤
        max (F n ω - (w x + (M n ω + B n ω))) 0 := le_max_left _ _
    calc
      F n ω ≤ max (F n ω - (w x + (M n ω + B n ω))) 0 +
          (w x + (M n ω + B n ω)) := (sub_le_iff_le_add.mp hm)
      _ = w x + (M n ω + B n ω) +
          max (F n ω - (w x + (M n ω + B n ω))) 0 + max (0 : ℝ) 0 := by
          simp only [max_self]
          ring
  · simpa only [max_self, integral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
