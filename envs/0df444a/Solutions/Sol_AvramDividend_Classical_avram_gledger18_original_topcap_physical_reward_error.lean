-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger18_original_topcap_physical_reward_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:59:00.91476+00:00
-- url     : https://prove2.me/submissions/d769ff15-4048-406a-b026-209b91f632e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger18_original_topcap_physical_grid_centered
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_bounded_stop_masked_strict_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_physical_sigma_clock_le_finite_horizon
import Theorems.Thm_AvramDividend_Classical_avram_gledger19_original_topcap_compact_stopped_reward_expected_upper
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-
This is a source-complete source-faithful reduction to one authoritative
Open child, with two Proved analytic prerequisites. Remote compilation is
required before acceptance; no local Lean compilation has been performed.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
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
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω =>
      if ζ ω = 0 then w x else
        Real.exp (-(q * (ζ ω : ℝ))) *
          w (riskProcess X x D (ζ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    ∀ ε : ℝ, 0 < ε →
      ∃ m : ℕ, 0 < m ∧
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let M : Ω → ℝ := fun ω =>
          ∑ i ∈ Finset.range m,
            let s : ℝ≥0 := (i : ℝ≥0) * Δ
            if s < ρ ω then
              let y := riskProcess X x D s ω
              let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
              Real.exp (-(q * (s : ℝ))) *
                (deriv w y * Z +
                  (iteratedDeriv 2 w y / 2) * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
            else 0
        Integrable (H ρ) P ∧
        Integrable (fun ω => H ρ ω - w x - M ω) P ∧
        (∫ ω, H ρ ω - w x - M ω ∂P) ≤ ε := by
  classical
  intro H ε hε
  letI : IsProbabilityMeasure P := X.isProbability
  have hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0) := by
    exact avram_f16_original_physical_sigma_clock_le_finite_horizon
      X x D n τ hτeq (fun _ => ρ)
        (by intro k ω; exact hρle ω) 0
  have hHI : Integrable (H ρ) P := by
    exact avram_ubv_gauss_top14_original_bounded_stop_masked_strict_reward_L1
      X hX hBV hNuZero q hq w C hC hTopCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x D hD ρ hρstop (n : ℝ≥0) hρbound
  -- Supply this source-exact theorem once its publication is verified.
  have hUpper : (∫ ω, H ρ ω ∂P) ≤ w x := by
    exact avram_gledger19_original_topcap_compact_stopped_reward_expected_upper
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  refine ⟨1, by omega, ?_⟩
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((1 : ℝ≥0) + 1)
  let M : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range 1,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let y := riskProcess X x D s ω
        let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        Real.exp (-(q * (s : ℝ))) *
          (deriv w y * Z +
            (iteratedDeriv 2 w y / 2) * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0
  have hMI : Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by
    simpa only [M, Δ, Nat.cast_one] using
      (avram_gledger18_original_topcap_physical_grid_centered
        X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
        hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
        x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτstop
        ρ hρstop hρle j hprefix 1 (by omega))
  -- The goal's mesh is elaborated under dependent `let` binders.  An
  -- explicit simplification bridge avoids relying on definitional equality
  -- with the locally named mesh and its NNReal numeral casts.
  suffices hGoal : Integrable (H ρ) P ∧
    Integrable (fun ω => H ρ ω - w x - M ω) P ∧
    (∫ ω, H ρ ω - w x - M ω ∂P) ≤ ε by
    simpa only [M, Δ, Nat.cast_one] using hGoal
  have hSubI : Integrable (fun ω => H ρ ω - w x) P :=
    hHI.sub (integrable_const _)
  refine ⟨hHI, hSubI.sub hMI.1, ?_⟩
  calc
    (∫ ω, H ρ ω - w x - M ω ∂P) =
        (∫ ω, H ρ ω - w x ∂P) - (∫ ω, M ω ∂P) :=
      integral_sub hSubI hMI.1
    _ = (∫ ω, H ρ ω ∂P) - w x := by
      rw [integral_sub hHI (integrable_const _), hMI.2]
      simp
    _ ≤ 0 := sub_nonpos.mpr hUpper
    _ ≤ ε := le_of_lt hε
