-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_topcap_strict_prefix_earlier_stopped_grid_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:36:12.03023+00:00
-- url     : https://prove2.me/submissions/fe223bd5-5f77-4a67-a4bc-4e0d8515132b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_strict_each_grid_real_signed_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_strict_prefix_double_clip_signed_grid_identity
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t ρ : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω)
    (n j i : ℕ) (htn : t ≤ (n : ℝ≥0))
    (hi : i ≤ (n + 1) * (j + 1))
    (hti : t = min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ) :
    let u : ℕ → ℝ≥0 := fun l =>
      min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
    (w (x - rightLimit D 0 ω) - w x) +
      (∑ l ∈ Finset.range i,
        Real.exp (-(q * (u (l + 1) : ℝ))) *
          (w (x + X.X (u (l + 1)) ω - rightLimit D (u (l + 1)) ω) -
           w (x + X.X (u (l + 1)) ω - rightLimit D (u l) ω))) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      (ENNReal.ofReal (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))).toReal := by
  let m : ℕ := (n + 1) * (j + 1)
  let u : ℕ → ℝ≥0 := fun l =>
    min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
  let v : ℕ → ℝ≥0 := fun l =>
    min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
  let g : ℝ≥0 → ℝ≥0 → ℝ := fun r l =>
    Real.exp (-(q * (r : ℝ))) *
      (w (x + X.X r ω - rightLimit D r ω) -
       w (x + X.X r ω - rightLimit D l ω))
  have hDiag : ∀ z, g z z = 0 := by
    intro z
    simp [g]
  have hPrefix0 :=
    avram_jump6_B_original_strict_prefix_double_clip_signed_grid_identity
      j m i hi ρ g hDiag
  have hPrefix :
      (∑ l ∈ Finset.range m, g (v (l + 1)) (v l)) =
      (∑ l ∈ Finset.range i, g (u (l + 1)) (u l)) := by
    simpa [v, u, m, hti] using hPrefix0
  let drop : ℕ → ℝ := fun l =>
    Real.exp (-(q * (v (l + 1) : ℝ))) *
      (w (x + X.X (v (l + 1)) ω - rightLimit D (v l) ω) -
       w (x + X.X (v (l + 1)) ω - rightLimit D (v (l + 1)) ω))
  have hNeg : (∑ l ∈ Finset.range m, drop l) =
      -(∑ l ∈ Finset.range m, g (v (l + 1)) (v l)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    dsimp [drop, g]
    ring
  have hBase :=
    avram_jump6_B_original_topcap_strict_each_grid_real_signed_cash
      X x C hC hTop q hq w hw_cont hw_smooth hw_grad
      hxc D hD ω t hStrict n htn j
  change
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
    (w (x - rightLimit D 0 ω) - w x) -
    (∑ l ∈ Finset.range m, drop l) ≤
    (ENNReal.ofReal (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
      dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))).toReal at hBase
  dsimp only
  change (w (x - rightLimit D 0 ω) - w x) +
    (∑ l ∈ Finset.range i, g (u (l + 1)) (u l)) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
    (ENNReal.ofReal (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
      dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))).toReal
  rw [← hPrefix]
  rw [hNeg] at hBase
  linarith only [hBase]