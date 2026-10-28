-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_jump_convolution_laplace_of_fubini
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:09:09.329651+00:00
-- url     : https://prove2.me/submissions/2b53aef8-ff8c-4302-9162-67830ec4c039

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shifted_laplace_transform
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem S190_W_monotone {W : ℝ → ℝ} (h0 : ∀ y < 0, W y = 0) (hnn : ∀ y, 0 ≤ y → 0 ≤ W y)
    (hm : MonotoneOn W (Ici 0)) : Monotone W := by
  intro a b hab
  by_cases ha : a < 0
  · rw [h0 a ha]
    by_cases hb : b < 0
    · rw [h0 b hb]
    · exact hnn b (not_lt.mp hb)
  · have ha' : 0 ≤ a := not_lt.mp ha
    exact hm (mem_Ici.mpr ha') (mem_Ici.mpr (ha'.trans hab)) hab

theorem S190_W_nonneg {W : ℝ → ℝ} (h0 : ∀ y < 0, W y = 0) (hnn : ∀ y, 0 ≤ y → 0 ≤ W y)
    (y : ℝ) : 0 ≤ W y := by
  by_cases hy : y < 0
  · rw [h0 y hy]
  · exact hnn y (not_lt.mp hy)

/-- `ν (Iic (-δ)) < ∞` for `δ > 0`. -/
theorem S190_nu_Iic_lt_top {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ) (hδ : 0 < δ) :
    X.ν (Iic (-δ)) < ⊤ := by
  have hc : 0 < min 1 (δ ^ 2) := lt_min one_pos (by positivity)
  have key : ENNReal.ofReal (min 1 (δ ^ 2)) * X.ν (Iic (-δ)) ≤
      ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν := by
    calc ENNReal.ofReal (min 1 (δ ^ 2)) * X.ν (Iic (-δ))
        = ∫⁻ y in Iic (-δ), ENNReal.ofReal (min 1 (δ ^ 2)) ∂X.ν := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ y in Iic (-δ), ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν := by
          refine setLIntegral_mono' measurableSet_Iic (fun y hy => ?_)
          apply ENNReal.ofReal_le_ofReal
          apply min_le_min le_rfl
          have : y ≤ -δ := hy
          nlinarith
      _ ≤ ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν := setLIntegral_le_lintegral _ _
  have hlt := lt_of_le_of_lt key X.ν_integrable
  have hpos : ENNReal.ofReal (min 1 (δ ^ 2)) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero]; exact hδ.ne'
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon, ENNReal.mul_top hpos] at hlt
  exact lt_irrefl _ hlt

theorem S190_nu_Ioo_top {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hinf : X.ν (Iio 0) = ⊤) (δ : ℝ) (hδ : 0 < δ) : X.ν (Ioo (-δ) 0) = ⊤ := by
  have hsub : Iio (0:ℝ) ⊆ Iic (-δ) ∪ Ioo (-δ) 0 := by
    intro y hy
    by_cases h : y ≤ -δ
    · exact Or.inl h
    · exact Or.inr ⟨not_le.mp h, hy⟩
  have := (measure_mono hsub).trans (measure_union_le (μ := X.ν) _ _)
  rw [hinf, top_le_iff] at this
  by_contra hne
  exact ENNReal.add_ne_top.mpr ⟨(S190_nu_Iic_lt_top X δ hδ).ne, hne⟩ this

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hfubini :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y))) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
    (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν) *
      (X.ψ θ - q)⁻¹ := by
  clear hfubini
  obtain ⟨h0, hnn, hcont, hmon, hlap⟩ := hW
  have hWmono : Monotone W := S190_W_monotone h0 hnn hmon
  have hWnn : ∀ y, 0 ≤ W y := S190_W_nonneg h0 hnn
  have hWm : Measurable W := hWmono.measurable
  have hWint := (hlap θ hθ hqθ).1
  by_cases hfin : X.ν (Iio 0) < ⊤
  · haveI : IsFiniteMeasure (X.ν.restrict (Iio 0)) :=
      isFiniteMeasure_restrict.mpr hfin.ne
    have hint : Integrable (Function.uncurry fun x y => Real.exp (-(θ * x)) * W (x + y))
        ((volume.restrict (Ioi (0:ℝ))).prod (X.ν.restrict (Iio 0))) := by
      refine Integrable.mono' (g := fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) * W p.1)
        (hWint.comp_fst _) ?_ ?_
      · apply Measurable.aestronglyMeasurable
        exact (Real.measurable_exp.comp (measurable_fst.const_mul θ).neg).mul
          (hWm.comp (measurable_fst.add measurable_snd))
      · have hae : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi (0:ℝ))).prod (X.ν.restrict (Iio 0))),
            p.2 ∈ Iio (0:ℝ) :=
          Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Iio)
        filter_upwards [hae] with p hp
        obtain ⟨x, y⟩ := p
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hWnn _))]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact hWmono (by have : y < 0 := hp; linarith)
    simp_rw [← integral_const_mul]
    rw [integral_integral_swap hint, ← integral_mul_const]
    refine setIntegral_congr_fun (μ := X.ν) (measurableSet_Iio : MeasurableSet (Iio (0:ℝ)))
      (fun y hy => ?_)
    exact scaleFunction_shifted_laplace_transform X q W ⟨h0, hnn, hcont, hmon, hlap⟩
      θ y hθ hqθ (le_of_lt (mem_Iio.mp hy))
  · have hinf : X.ν (Iio 0) = ⊤ := top_le_iff.mp (not_lt.mp hfin)
    -- RHS is zero
    have hR : ¬ Integrable (fun y => Real.exp (θ * y)) (X.ν.restrict (Iio 0)) := by
      intro hI
      have h1 := hI.2
      unfold HasFiniteIntegral at h1
      have hle : ENNReal.ofReal (Real.exp (-θ)) * X.ν (Ioo (-1) 0) ≤
          ∫⁻ y in Iio (0:ℝ), ‖Real.exp (θ * y)‖ₑ ∂X.ν := by
        calc ENNReal.ofReal (Real.exp (-θ)) * X.ν (Ioo (-1) 0)
            = ∫⁻ y in Ioo (-1:ℝ) 0, ENNReal.ofReal (Real.exp (-θ)) ∂X.ν := by
              rw [setLIntegral_const]
          _ ≤ ∫⁻ y in Ioo (-1:ℝ) 0, ‖Real.exp (θ * y)‖ₑ ∂X.ν := by
              refine setLIntegral_mono' measurableSet_Ioo (fun y hy => ?_)
              rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
              apply ENNReal.ofReal_le_ofReal
              apply Real.exp_le_exp.mpr
              have : -1 < y := hy.1
              nlinarith
          _ ≤ ∫⁻ y in Iio (0:ℝ), ‖Real.exp (θ * y)‖ₑ ∂X.ν :=
              lintegral_mono_set Ioo_subset_Iio_self
      rw [S190_nu_Ioo_top X hinf 1 one_pos,
        ENNReal.mul_top (by simp [Real.exp_pos])] at hle
      exact absurd (lt_of_le_of_lt hle h1) (lt_irrefl _)
    rw [integral_undef hR, zero_mul]
    -- LHS is zero
    have hinner : ∀ x : ℝ, 0 < x → (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν) = 0 := by
      intro x hx
      by_cases hWx : W x = 0
      · apply setIntegral_eq_zero_of_forall_eq_zero
        intro y hy
        have := hWmono (show x + y ≤ x by have : y < 0 := hy; linarith)
        linarith [hWnn (x + y)]
      · have hWxpos : 0 < W x := lt_of_le_of_ne (hWnn x) (Ne.symm hWx)
        -- find δ with W (x - δ) > 0
        have hcw : ContinuousWithinAt W (Ici 0) x := hcont x (mem_Ici.mpr hx.le)
        have hev : ∀ᶠ z in nhdsWithin x (Ici 0), W x / 2 < W z :=
          hcw.eventually (lt_mem_nhds (by linarith))
        rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
        obtain ⟨ε, hε, hball⟩ := hev
        set δ := min (ε / 2) (min (x / 2) (1 / 2)) with hδdef
        have hδpos : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
        have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hδx : δ < x := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
          (by linarith)
        have hWd : W x / 2 < W (x - δ) := by
          apply hball
          · rw [Real.dist_eq, show x - δ - x = -δ by ring, abs_neg, abs_of_pos hδpos]
            exact hδε
          · exact mem_Ici.mpr (by linarith)
        apply integral_undef
        intro hI
        have h1 := hI.2
        unfold HasFiniteIntegral at h1
        have hle : ENNReal.ofReal (W (x - δ)) * X.ν (Ioo (-δ) 0) ≤
            ∫⁻ y in Iio (0:ℝ), ‖W (x + y)‖ₑ ∂X.ν := by
          calc ENNReal.ofReal (W (x - δ)) * X.ν (Ioo (-δ) 0)
              = ∫⁻ y in Ioo (-δ) 0, ENNReal.ofReal (W (x - δ)) ∂X.ν := by
                rw [setLIntegral_const]
            _ ≤ ∫⁻ y in Ioo (-δ) 0, ‖W (x + y)‖ₑ ∂X.ν := by
                refine setLIntegral_mono' measurableSet_Ioo (fun y hy => ?_)
                rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hWnn _)]
                apply ENNReal.ofReal_le_ofReal
                apply hWmono
                have : -δ < y := hy.1
                linarith
            _ ≤ ∫⁻ y in Iio (0:ℝ), ‖W (x + y)‖ₑ ∂X.ν :=
                lintegral_mono_set Ioo_subset_Iio_self
        rw [S190_nu_Ioo_top X hinf δ hδpos,
          ENNReal.mul_top (by simp; linarith)] at hle
        exact absurd (lt_of_le_of_lt hle h1) (lt_irrefl _)
    rw [setIntegral_congr_fun (g := fun _ => (0:ℝ)) measurableSet_Ioi
      (fun x hx => by simp only; rw [hinner x hx, mul_zero])]
    simp

