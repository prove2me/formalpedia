-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva33_finitecap_finiteactivity_exact_B_grid_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T21:54:15.417377+00:00
-- url     : https://prove2.me/submissions/58b4e424-b2a3-4039-87a5-af1e42162fcf

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva31_original_BV_physical_drift_jump_R_vanishes
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_original_finitecap_HJB_grid_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
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
    (hCapFinite : C ≠ ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∃ B : ℕ → Ω → ℝ,
      (∀ n ω,
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
             else 0) * (R (u n i) - R (u n (i + 1))))) ∧
      (∀ n, Integrable (B n) P) := by
  classical
  intro δ S
  let G : ℕ → Ω → ℝ := fun n ω =>
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    ∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
  let B : ℕ → Ω → ℝ := fun n ω =>
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    G n ω +
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
        else 0) * (R (u n i) - R (u n (i + 1))))
  have hG : ∀ n, Integrable (G n) P := by
    intro n
    simpa only [G] using
      (avram_bv_correct12_original_finitecap_HJB_grid_L1
        X hX hBV q hq w C hC hCapFinite hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump hActivity
        T hT u hgrid hmono huniform n)
  have hBG (n : ℕ) : B n =ᵐ[P] G n := by
    filter_upwards
      [avram_bva31_original_BV_physical_drift_jump_R_vanishes X hX hBV]
      with ω hR
    simp [B, G, hR]
  refine ⟨B, (by intro n ω; rfl), ?_⟩
  intro n; exact (hG n).congr (hBG n).symm
