-- Prove2me | solution 1 for FeynmanKac.discounted_gradient_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:48:22.814278+00:00
-- url     : https://prove2.me/submissions/63acf729-3031-4885-9d18-6cae924492c9

import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_FeynmanKac_PathDiscount
import Mathlib

open MeasureTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ)
    (huC12 : m.IsC12 u)
    (hu : m.BoundedSpatialGradient u) :
    m.SquareIntegrableDiscountedGradient u := by
  obtain ⟨hm, hp, hq, hV⟩ := m.isDiffusion
  have hcont : ∀ ω, Continuous fun t => m.augmentedPath t ω := hV.continuous_path
  have hmeas : ∀ t, Measurable (m.augmentedPath t) := fun t =>
    ((hV.adapted t).mono (m.filtration.le t)).measurable
  have hjoint : Measurable (Function.uncurry m.augmentedPath) :=
    measurable_uncurry_of_continuous_of_measurable hcont hmeas
  have hpathc : ∀ ω, Continuous fun s => m.path s ω := fun ω =>
    (continuous_apply 0).comp ((hcont ω).comp (continuous_id.sub continuous_const))
  have hpathj : Measurable fun z : ℝ × Ω => m.path z.1 z.2 := by
    have : Measurable fun z : ℝ × Ω => m.augmentedPath (z.1 - m.initialTime) z.2 :=
      hjoint.comp ((measurable_fst.sub_const _).prodMk measurable_snd)
    exact (measurable_pi_apply 0).comp this
  have hVc : Continuous fun z : ℝ × ℝ => m.potential z.1 z.2 := m.potential_continuous
  have hVpath : ∀ ω, Continuous fun r => m.potential (m.path r ω) r := fun ω =>
    hVc.comp ((hpathc ω).prodMk continuous_id)
  have hVj : Measurable fun z : ℝ × Ω => m.potential (m.path z.1 z.2) z.1 :=
    hVc.measurable.comp (hpathj.prodMk measurable_fst)
  -- the discount factor is jointly measurable
  have hdc : ∀ ω, Continuous fun s => m.pathDiscount s ω := by
    intro ω
    unfold FeynmanKac.BoundedDiffusionModel.pathDiscount FeynmanKac.pathDiscount
    exact Real.continuous_exp.comp
      ((intervalIntegral.continuous_primitive
        (fun a b => (hVpath ω).intervalIntegrable a b) _).neg)
  have hIoc : ∀ (g : ℝ × Ω → ℝ), Measurable g → ∀ a b : ℝ,
      Measurable fun ω => ∫ r in a..b, g (r, ω) := by
    intro g hg a b
    simp only [intervalIntegral]
    exact ((hg.stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict (Set.Ioc a b))).measurable).sub
      ((hg.stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict (Set.Ioc b a))).measurable)
  have hdm : ∀ s, Measurable fun ω => m.pathDiscount s ω := by
    intro s
    unfold FeynmanKac.BoundedDiffusionModel.pathDiscount FeynmanKac.pathDiscount
    exact Real.measurable_exp.comp (hIoc _ hVj _ _).neg
  have hdj : Measurable fun z : ℝ × Ω => m.pathDiscount z.1 z.2 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun s ω => m.pathDiscount s ω) hdc hdm
  -- volatility
  have hσ : ∀ x s, m.volatility x s = m.augmentedVolatility ![x, s] 0 0 := by
    intro x s; rw [m.augmentedVolatility_space]; simp
  have hvec : Continuous fun z : ℝ × ℝ => (![z.1, z.2] : Fin 2 → ℝ) := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have hσc : Continuous fun z : ℝ × ℝ => m.volatility z.1 z.2 := by
    simp_rw [hσ]
    exact (continuous_apply 0).comp (m.augmentedVolatility_continuous.comp hvec)
  obtain ⟨Bv, hBv⟩ := m.augmentedVolatility_bounded
  have hσb : ∀ x s, |m.volatility x s| ≤ Bv := by
    intro x s; rw [hσ]
    exact (norm_le_pi_norm (m.augmentedVolatility ![x, s] 0) 0).trans (hBv _)
  have hgc : Continuous fun z : ℝ × ℝ => deriv (fun x => u x z.2) z.1 := huC12.2.2.2.2.2.1
  obtain ⟨Bg, hBg⟩ := hu
  have hFj : Measurable fun z : ℝ × Ω =>
      m.pathDiscount z.1 z.2 * m.volatility (m.path z.1 z.2) z.1 *
        deriv (fun x => u x z.1) (m.path z.1 z.2) :=
    (hdj.mul (hσc.measurable.comp (hpathj.prodMk measurable_fst))).mul
      (hgc.measurable.comp (hpathj.prodMk measurable_fst))
  refine ⟨hFj, ?_⟩
  have hGm : Measurable fun ω => ∫ s in m.initialTime..m.terminalTime,
      (m.pathDiscount s ω * m.volatility (m.path s ω) s *
        deriv (fun x => u x s) (m.path s ω)) ^ 2 :=
    hIoc _ (hFj.pow_const 2) _ _
  refine Integrable.mono' (integrable_const ((Bv * Bg) ^ 2 * |m.terminalTime - m.initialTime|))
    hGm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
  rw [Set.uIoc_of_le m.horizon_nonneg] at hs
  have hsI : s ∈ Set.Icc m.initialTime m.terminalTime := ⟨hs.1.le, hs.2⟩
  have hd1 : |m.pathDiscount s ω| ≤ 1 := by
    unfold FeynmanKac.BoundedDiffusionModel.pathDiscount FeynmanKac.pathDiscount
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact intervalIntegral.integral_nonneg hs.1.le fun r _ => m.potential_nonneg _ _
  have hv := hσb (m.path s ω) s
  have hg := hBg (m.path s ω) s hsI
  have hBv0 : 0 ≤ Bv := (abs_nonneg _).trans hv
  have hF : |m.pathDiscount s ω * m.volatility (m.path s ω) s *
      deriv (fun x => u x s) (m.path s ω)| ≤ Bv * Bg := by
    rw [abs_mul, abs_mul]
    calc |m.pathDiscount s ω| * |m.volatility (m.path s ω) s| *
          |deriv (fun x => u x s) (m.path s ω)| ≤ 1 * Bv * Bg := by gcongr
      _ = Bv * Bg := by ring
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hF 2
