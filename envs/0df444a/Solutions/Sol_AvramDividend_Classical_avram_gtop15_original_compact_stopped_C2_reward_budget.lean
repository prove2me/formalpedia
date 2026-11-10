-- Prove2me | solution 1 for AvramDividend.Classical.avram_gtop15_original_compact_stopped_C2_reward_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T00:57:25.58998+00:00
-- url     : https://prove2.me/submissions/15b5dafc-8993-405d-8036-e1707c2ad2b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger18_original_topcap_physical_gaussian_grid_error_certificate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    (∫ ω, H ρ ω ∂P) ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω =>
    if ζ ω = 0 then w x else
      Real.exp (-(q * (ζ ω : ℝ))) *
        w (riskProcess X x D (ζ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
  change (∫ ω, H ρ ω ∂P) ≤ w x
  have hcertificate :=
    avram_gledger18_original_topcap_physical_gaussian_grid_error_certificate
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  by_contra hbound
  have hpositive : 0 < (∫ ω, H ρ ω ∂P) - w x :=
    sub_pos.mpr (lt_of_not_ge hbound)
  have hε : 0 < ((∫ ω, H ρ ω ∂P) - w x) / 2 :=
    half_pos hpositive
  obtain ⟨m, hm, hMI, hMzero, hHI, hres⟩ :=
    hcertificate (((∫ ω, H ρ ω ∂P) - w x) / 2) hε
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
  change Integrable M P at hMI
  change (∫ ω, M ω ∂P) = 0 at hMzero
  change (∫ ω, H ρ ω - w x - M ω ∂P) ≤
    ((∫ ω, H ρ ω ∂P) - w x) / 2 at hres
  have hconstant : Integrable (fun _ : Ω => w x) P :=
    integrable_const _
  have hsplit :
      (∫ ω, H ρ ω - w x - M ω ∂P) =
        (∫ ω, H ρ ω ∂P) - w x := by
    calc
      _ = ∫ ω, ((H ρ - (fun _ : Ω => w x)) - M) ω ∂P := rfl
      _ = (∫ ω, (H ρ - (fun _ : Ω => w x)) ω ∂P) -
            (∫ ω, M ω ∂P) :=
        integral_sub (hHI.sub hconstant) hMI
      _ = (∫ ω, H ρ ω ∂P) - w x := by
        change (∫ ω, H ρ ω - w x ∂P) - (∫ ω, M ω ∂P) =
          (∫ ω, H ρ ω ∂P) - w x
        rw [integral_sub hHI hconstant, hMzero]
        simp
        all_goals rfl
  rw [hsplit] at hres
  linarith
