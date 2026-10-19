-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_generatorIntegrable_above
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:38:57.58254+00:00
-- url     : https://prove2.me/submissions/1c7eccf0-be56-4e03-88f0-8fe6027ffaaa

import Mathlib
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Filter Topology
open AvramDividend.Classical
open scoped NNReal ENNReal

open MeasureTheory Set Filter Topology AvramDividend.Classical in
open scoped NNReal ENNReal in
theorem hn2_levy_mass_finite {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ) (hδ : 0 < δ) :
    X.ν (Iic (-δ)) < ⊤ := by
  set m : ℝ≥0∞ := ENNReal.ofReal (min 1 (δ^2)) with hm
  have hm0 : m ≠ 0 := by
    rw [hm]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_min one_pos (by positivity)
  have hsub : Iic (-δ) ⊆ {y | m ≤ ENNReal.ofReal (min 1 (y^2))} := by
    intro y hy
    simp only [mem_Iic] at hy
    simp only [mem_setOf_eq, hm]
    apply ENNReal.ofReal_le_ofReal
    apply min_le_min_left
    nlinarith
  have h1 := mul_meas_ge_le_lintegral₀ (μ := X.ν)
    (f := fun y => ENNReal.ofReal (min 1 (y^2))) (by fun_prop) m
  have h2 : m * X.ν (Iic (-δ)) ≤ m * X.ν {y | m ≤ ENNReal.ofReal (min 1 (y^2))} :=
    by gcongr
  exact ENNReal.lt_top_of_mul_ne_top_right ((h2.trans h1).trans_lt X.ν_integrable).ne hm0

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : a < x) :
    X.GeneratorIntegrable (barrierValue W a) x := by
  classical
  set d := scaleDeriv W a with hd
  set f := barrierValue W a with hf
  set C : ℝ := |divE (W a) d| + (x - a) with hC
  have hWm : Measurable W := by
    have : W = (Ici (0:ℝ)).piecewise W 0 := by
      funext z
      by_cases hz : z ∈ Ici (0:ℝ)
      · simp [Set.piecewise, hz]
      · simp only [Set.piecewise, hz, if_false, Pi.zero_apply]
        exact hW.1 z (by simpa using hz)
    rw [this]
    exact ContinuousOn.measurable_piecewise hW.2.2.1 continuousOn_const measurableSet_Ici
  have hdivm : Measurable (fun z => divE (W z) d) := by
    unfold divE; split_ifs
    · exact measurable_const
    · exact hWm.div_const _
  have hfm : Measurable f := by
    have : f = fun z => if z < 0 then 0 else if z ≤ a then divE (W z) d else z - a + divE (W a) d := rfl
    rw [this]
    refine Measurable.ite measurableSet_Iio measurable_const ?_
    exact Measurable.ite measurableSet_Iic hdivm (by fun_prop)
  -- bound on (-∞, x]
  have hbd : ∀ z, z ≤ x → |f z| ≤ C := by
    intro z hz
    have hdiv : ∀ u, 0 ≤ u → u ≤ a → |divE (W u) d| ≤ |divE (W a) d| := by
      intro u hu hua
      have hWu := hW.2.1 u hu
      have hWa := hW.2.2.2.1 (mem_Ici.mpr hu) (mem_Ici.mpr ha) hua
      unfold divE; split_ifs
      · simp
      · rw [abs_div, abs_div, abs_of_nonneg hWu, abs_of_nonneg (hW.2.1 a ha)]
        exact div_le_div_of_nonneg_right hWa (abs_nonneg _)
    simp only [hf, barrierValue]
    split_ifs with h1 h2
    · simp only [abs_zero]; rw [hC]; positivity
    · rw [hC]; linarith [hdiv z (not_lt.mp h1) h2]
    · rw [hC]
      have : |z - a + divE (W a) d| ≤ |z - a| + |divE (W a) d| := abs_add_le _ _
      have : |z - a| = z - a := abs_of_nonneg (by linarith [not_le.mp h2])
      linarith
  -- local form near x
  have hloc : f =ᶠ[𝓝 x] fun z => z - a + divE (W a) d := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    simp only [mem_Ioi] at hz
    simp only [hf, barrierValue, if_neg (show ¬ z < 0 by linarith), if_neg (show ¬ z ≤ a by linarith), hd]
  have hD : deriv f x = 1 := by
    rw [hloc.deriv_eq]
    simp
  have hfx : f x = x - a + divE (W a) d := hloc.eq_of_nhds
  set ε := min (x - a) 1 with hε
  have hε0 : 0 < ε := lt_min (by linarith) one_pos
  have hsplit : Iio (0:ℝ) ⊆ Iic (-ε) ∪ Ioo (-ε) 0 := by
    intro y hy
    simp only [mem_Iio] at hy
    by_cases h : y ≤ -ε
    · exact Or.inl h
    · exact Or.inr ⟨by linarith [not_le.mp h], hy⟩
  unfold SpectrallyNegativeLevy.GeneratorIntegrable
  refine IntegrableOn.mono_set (IntegrableOn.union ?_ ?_) hsplit
  · -- bounded on a finite-measure set
    have hfin := hn2_levy_mass_finite X ε hε0
    have hmeas : Measurable (SpectrallyNegativeLevy.generatorIntegrand f x) := by
      unfold SpectrallyNegativeLevy.generatorIntegrand
      have : Measurable fun y => f (x + y) := hfm.comp (measurable_const_add x)
      refine (this.sub measurable_const).sub ?_
      exact (measurable_const.mul measurable_id).mul (measurable_const.indicator measurableSet_Ioo)
    refine Integrable.mono' (g := fun _ => C + C + |deriv f x|) ?_ hmeas.aestronglyMeasurable ?_
    · exact (integrableOn_const_iff).mpr (Or.inr hfin)
    · rw [ae_restrict_iff' measurableSet_Iic]
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      simp only [mem_Iic] at hy
      unfold SpectrallyNegativeLevy.generatorIntegrand
      have h1 := hbd (x + y) (by linarith)
      have h2 := hbd x le_rfl
      have h3 : |deriv f x * y * (Ioo (-1:ℝ) 1).indicator 1 y| ≤ |deriv f x| := by
        by_cases hy1 : y ∈ Ioo (-1:ℝ) 1
        · rw [Set.indicator_of_mem hy1, Pi.one_apply, mul_one, abs_mul]
          have : |y| ≤ 1 := by rw [abs_le]; exact ⟨hy1.1.le, hy1.2.le⟩
          nlinarith [abs_nonneg (deriv f x)]
        · rw [Set.indicator_of_notMem hy1, mul_zero, abs_zero]; exact abs_nonneg _
      rw [Real.norm_eq_abs]
      calc |f (x + y) - f x - deriv f x * y * (Ioo (-1:ℝ) 1).indicator 1 y|
          ≤ |f (x + y)| + |f x| + |deriv f x * y * (Ioo (-1:ℝ) 1).indicator 1 y| := by
            have := abs_sub (f (x+y) - f x) (deriv f x * y * (Ioo (-1:ℝ) 1).indicator 1 y)
            have := abs_sub (f (x+y)) (f x)
            linarith
        _ ≤ C + C + |deriv f x| := by linarith
  · -- vanishes near 0
    refine (integrableOn_zero).congr_fun (fun y hy => ?_) measurableSet_Ioo
    simp only [mem_Ioo] at hy
    have hε1 : ε ≤ x - a := min_le_left _ _
    have hε2 : ε ≤ 1 := min_le_right _ _
    unfold SpectrallyNegativeLevy.generatorIntegrand
    have hxy : f (x + y) = x + y - a + divE (W a) d := by
      simp only [hf, barrierValue, if_neg (show ¬ x + y < 0 by linarith),
        if_neg (show ¬ x + y ≤ a by linarith), hd]
    have hin : y ∈ Ioo (-1:ℝ) 1 := ⟨by linarith, by linarith⟩
    rw [hxy, hfx, hD, Set.indicator_of_mem hin, Pi.one_apply]
    ring

