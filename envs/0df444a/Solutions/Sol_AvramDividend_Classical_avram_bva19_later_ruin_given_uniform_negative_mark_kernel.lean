-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva19_later_ruin_given_uniform_negative_mark_kernel
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:00:32.782809+00:00
-- url     : https://prove2.me/submissions/063c127d-37c2-4d2e-b7cb-973755dd0370
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva19_original_inclusive_compensator_grid_converges
import Theorems.Thm_AvramDividend_Classical_avram_bva19_closed_grid_negative_gain_le_open_grid
import Theorems.Thm_AvramDividend_Classical_avram_bva19_positive_part_from_closed_grid_approximation
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (hFinite : C ≠ ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) (hMassPos : 0 < X.ν (Iio (0 : ℝ))) (hKernel : ∀ s : Set ℝ, IsCompact s →
      s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} →
      UniformContinuousOn
        (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) s)
    (ω : Ω) (hRuinNonzero : ruinTime X x D ω ≠ 0) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let K : ℕ → Ω → ℝ := fun n ω =>
      (∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal))
    let J : ℕ → Ω → ℝ := fun n ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      ∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          (∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
            (w (Z i + z) - w (Z i)) ∂X.ν) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0
    (∀ t : ℝ≥0, t ≤ S → X.X t ω = (t : ℝ) * X.drift) →
      (NX ω) (Ioc (0 : ℝ≥0) S ×ˢ Iio (0 : ℝ)) = 0 →
      Tendsto (fun n => if ruinTime X x D ω = 0 then 0 else
        max (K n ω - J n ω) 0) atTop (𝓝 0) := by
  intro δ S U H NX K J hSource hNoJump
  let A : ℕ → Ω → ℝ := fun n ω => let Z : ℕ → ℝ := fun i => U (u n i) ω
    ∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 ≤ Z i ∧ ENNReal.ofReal (Z i) ≤ C then
        (∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z i + z) - w (Z i)) ∂X.ν) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
  have hApprox : Tendsto (fun n => K n ω - A n ω) atTop (𝓝 (0 : ℝ)) :=
    avram_bva19_original_inclusive_compensator_grid_converges
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
      x hx hxc D hD T hT u hgrid hmono huniform hFinite hActivity
      hMassPos hKernel ω hRuinNonzero hSource hNoJump
  have hψ : ∀ b : ℝ, 0 ≤ b → ENNReal.ofReal b ≤ C →
      (∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) ≤ 0 := by
    intro b hb hbC; exact avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
      C hC w hw_cont hw0 hw_neg hw_smooth hw_grad X.ν b hb hbC
  have hSigned : ∀ n, A n ω ≤ J n ω := by
    intro n
    have h := avram_bva19_closed_grid_negative_gain_le_open_grid
      C u hmono (ruinTime X x D ω) (fun t => U t ω) q
      (fun b => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) hψ n
    simpa only [A, J, integral_const_mul] using h
  have hSqueeze := avram_bva19_positive_part_from_closed_grid_approximation
    (fun n => K n ω) (fun n => A n ω) (fun n => J n ω) hApprox hSigned
  simpa [hRuinNonzero] using hSqueeze
