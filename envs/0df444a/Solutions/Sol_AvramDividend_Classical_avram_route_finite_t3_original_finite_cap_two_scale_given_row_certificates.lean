-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_finite_t3_original_finite_cap_two_scale_given_row_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:54:28.201958+00:00
-- url     : https://prove2.me/submissions/64e97130-71cf-43f5-b78e-f9a4d3279c21
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_original_physical_stopped_residual_for_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- The one-scale physical-mesh certificate supplies the two-scale
finite-cap source, with a zero contact error and an arbitrary second index. -/
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
    (hAllB : ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0)
    (hPre : ∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω)
    (hFinite : C ≠ ⊤) :
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
            (∫ ω, max (ErrContact n k ω) 0 ∂P) ≤ η n + ε) := by
  dsimp only
  obtain ⟨M₀, B₀, E₀, hB₀, hM₀, hEI₀, hEzero, hBudget₀⟩ :=
    avram_a19_original_physical_stopped_residual_for_grid
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT u hgrid hmono
  have hBeq (n : ℕ) (ω : Ω) : B₀ n ω = B n ω := by
    exact (hB₀ n ω).trans (hB n ω).symm
  let η : ℕ → ℝ := fun n =>
    (∫ ω, max (E₀ n ω) 0 ∂P) + (1 : ℝ) / ((n : ℝ) + 1)
  have hNonneg (n : ℕ) :
      0 ≤ ∫ ω, max (E₀ n ω) 0 ∂P := by
    apply integral_nonneg
    intro ω
    exact le_max_right _ _
  have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (nhds (0 : ℝ)))
  have hη : Tendsto η atTop (nhds (0 : ℝ)) := by
    simpa [η] using hEzero.add hInv
  refine ⟨(fun n _ ω => M₀ n ω), (fun n _ ω => E₀ n ω),
    (fun _ _ _ => 0), η, ?_, hη, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp [η]
    exact add_pos_of_nonneg_of_pos (hNonneg n) (one_div_pos.mpr (by positivity))
  · intro n k
    exact ⟨(hM₀ n).1, (hM₀ n).2.1⟩
  · intro n k
    exact hEI₀ n
  · intro n k
    simp
  · intro n k
    filter_upwards [hBudget₀ n] with ω hω
    simpa only [hBeq n ω, max_self, add_zero] using hω
  · intro n ε hε
    refine ⟨0, ?_⟩
    simp only [max_self, integral_zero, add_zero]
    dsimp [η]
    have hpositive : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := le_of_lt (one_div_pos.mpr (by positivity))
    linarith
