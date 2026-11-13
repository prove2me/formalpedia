-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb30_original_finite_mark_floor_uniform_signed_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:08:47.449198+00:00
-- url     : https://prove2.me/submissions/ec58be3f-b3b6-4af3-b520-bf2903fb05aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_original_closed_cap_mark_kernel_uniform_bound
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
    (ω : Ω) (hRuinNonzero : ruinTime X x D ω ≠ 0)
    (hSource : ∀ r : ℝ≥0, r ≤ (⟨T, le_of_lt hT⟩ : ℝ≥0) →
      X.X r ω = (r : ℝ) * X.drift) :
    let U : ℝ≥0 → ℝ := fun t =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t
    let ψ : ℝ → ℝ := fun b =>
      ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν
    let rate : ℝ≥0 → ℝ := fun t =>
      Real.exp (-(q * (t : ℝ))) * ψ (U t)
    let μ : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal
    let F : ℕ → ℝ → ℝ := fun n r =>
      if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
        let i : ℕ := ⌊(r / T) * ((n : ℝ) + 2)⌋₊
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
           0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C
        then rate (u n i) else 0
      else 0
    let G : ℕ → ℝ → ℝ := fun n r =>
      let t : ℝ≥0 := Real.toNNReal r
      if 0 < r ∧ r < T - T / ((n : ℝ) + 2) ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then rate t else 0
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ n r, ‖F n r‖ ≤ B) ∧
      (∀ n r, ‖G n r‖ ≤ B) := by
  intro U ψ rate μ F G
  obtain ⟨B, hB, hψ⟩ :=
    avram_bva20_original_closed_cap_mark_kernel_uniform_bound
      C hFinite ψ hKernel
  have hRate (t : ℝ≥0) (ht : 0 ≤ U t)
      (htC : ENNReal.ofReal (U t) ≤ C) : ‖rate t‖ ≤ B := by
    change ‖Real.exp (-(q * (t : ℝ))) * ψ (U t)‖ ≤ B
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hqt : 0 ≤ q * (t : ℝ) :=
      mul_nonneg (le_of_lt hq) t.property
    have he : Real.exp (-(q * (t : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqt)
    calc
      Real.exp (-(q * (t : ℝ))) * |ψ (U t)| ≤
          1 * |ψ (U t)| :=
        mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ = |ψ (U t)| := one_mul _
      _ ≤ B := hψ (U t) ht htC
  refine ⟨B, hB, ?_, ?_⟩
  · intro n r
    dsimp only [F]
    split_ifs with hOuter hInner
    · exact hRate _ hInner.2.1 hInner.2.2
    · simpa using hB
    · simpa using hB
  · intro n r
    dsimp only [G]
    split_ifs with hInner
    · exact hRate _ hInner.2.2.2.1 hInner.2.2.2.2
    · simpa using hB
