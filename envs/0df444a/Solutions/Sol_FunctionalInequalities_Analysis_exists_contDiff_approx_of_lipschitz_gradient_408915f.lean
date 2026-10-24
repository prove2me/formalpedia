-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_contDiff_approx_of_lipschitz_gradient_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:43:04.011871+00:00
-- url     : https://prove2.me/submissions/039791a0-3eab-47a8-802a-ceca15114301

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Theorems.Thm_FunctionalInequalities_Analysis_gradient_convolution_normed_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hasFDerivAt_convolution_normed_of_lipschitz_408915f

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section NormedSpace
variable [NormedSpace ℝ E]
private lemma FunctionalInequalities.Analysis.integrable_mul_of_compact_support
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [OpensMeasurableSpace E]
    {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hcf : HasCompactSupport f) :
    Integrable (fun x => f x * g x) μ := by
  apply (hf.mul hg).integrable_of_hasCompactSupport
  refine hcf.mono ?_
  intro x hx
  by_contra hfx
  have hfx' : f x = 0 := by
    simpa [Function.mem_support] using hfx
  have hzero : (f * g) x = 0 := by
    simp only [Pi.mul_apply, hfx', zero_mul]
  exact hx hzero
private lemma FunctionalInequalities.Analysis.integrable_smul_of_compact_support
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ} {g : E → F} (hf : Continuous f) (hg : Continuous g)
    (hcf : HasCompactSupport f) :
    Integrable (fun x => f x • g x) μ := by
  apply (hf.smul hg).integrable_of_hasCompactSupport
  refine hcf.mono ?_
  intro x hx
  by_contra hfx
  have hfx' : f x = 0 := by
    simpa [Function.mem_support] using hfx
  have hzero : f x • g x = 0 := by
    simp only [hfx', zero_smul]
  exact hx hzero
end NormedSpace
section FiniteDimensional
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private lemma FunctionalInequalities.Analysis.locallyIntegrable_fderiv_gradient
    {U : E → ℝ} {G : NNReal} (hG : LipschitzWith G (gradient U)) :
    LocallyIntegrable (fderiv ℝ (gradient U)) (volume : Measure E) := by
  refine
    (continuous_const.locallyIntegrable :
      LocallyIntegrable (fun _ : E => (G : ℝ)) (volume : Measure E)).mono
      (measurable_fderiv (𝕜 := ℝ) (f := gradient U)).aestronglyMeasurable ?_
  filter_upwards [] with x
  simpa using norm_fderiv_le_of_lipschitz ℝ hG
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
theorem solution
    {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal} (hG : LipschitzWith G (gradient U)) :
    ∃ Uk : ℕ → E → ℝ, (∀ k, ContDiff ℝ ∞ (Uk k)) ∧
      (∀ k x, ‖gradient (Uk k) x - gradient U x‖ ≤ G / ((k : ℝ) + 1)) ∧
      (∀ k, LipschitzWith G (gradient (Uk k))) ∧
      (∀ x, Tendsto (fun k => Uk k x) atTop (𝓝 (U x))) ∧
      (∀ᵐ x ∂(volume : Measure E), Tendsto (fun k => fderiv ℝ (gradient (Uk k)) x) atTop
        (𝓝 (fderiv ℝ (gradient U) x))) := by
  classical
  let φ : ℕ → ContDiffBump (0 : E) := fun k =>
    ContDiffBump.mk
      (1 / (2 * ((k : ℝ) + 1)))
      (1 / ((k : ℝ) + 1))
      (by positivity)
      (by
        have hk : 0 < (k : ℝ) + 1 := by positivity
        apply (div_lt_div_iff₀ (by positivity) hk).2
        nlinarith)
  let Uk : ℕ → E → ℝ := fun k =>
    convolution
      ((φ k).normed (volume : Measure E)) U
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E)
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
    dsimp [φ]
    have hnat : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop := by
      rw [tendsto_atTop]
      intro a
      rcases exists_nat_gt a with ⟨n, hn⟩
      filter_upwards [eventually_ge_atTop n] with k hk
      have hk' : (n : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast hk
      linarith
    convert tendsto_inv_atTop_zero.comp hnat using 1
    ext k
    simp only [Function.comp_apply, one_div]
  have hφ' : ∀ᶠ k : ℕ in atTop, (φ k).rOut ≤ 2 * (φ k).rIn := by
    filter_upwards [] with k
    dsimp [φ]
    have hk : 0 < (k : ℝ) + 1 := by positivity
    field_simp
    norm_num
  have hUloc : LocallyIntegrable U (volume : Measure E) :=
    hU.continuous.locallyIntegrable
  have hgradloc :
      LocallyIntegrable (fderiv ℝ (gradient U)) (volume : Measure E) :=
    locallyIntegrable_fderiv_gradient hG
  have hmeas : AEStronglyMeasurable (gradient U) (volume : Measure E) :=
    (LipschitzWith.continuous hG).aestronglyMeasurable
  have hgrad : ∀ k,
      gradient (Uk k) =
        convolution
          ((φ k).normed (volume : Measure E)) (gradient U)
          (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E) := by
    intro k
    dsimp [Uk]
    exact FunctionalInequalities.Analysis.gradient_convolution_normed_408915f hU hG (φ k)
  refine ⟨Uk, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    dsimp [Uk]
    exact
      HasCompactSupport.contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ k).hasCompactSupport_normed
        (φ k).contDiff_normed
        hUloc
  · intro k x
    rw [hgrad k]
    have hdist :=
      ContDiffBump.dist_normed_convolution_le
        (φ := φ k) (x₀ := x) (ε := (G : ℝ) / ((k : ℝ) + 1)) hmeas
        (by
          intro y hy
          have hy' : dist y x < (φ k).rOut := hy
          have hh := hG.dist_le_mul y x
          have hG' : 0 ≤ (G : ℝ) := by positivity
          have hle :
              dist (gradient U y) (gradient U x) ≤
                (G : ℝ) / ((k : ℝ) + 1) := by
            calc
              dist (gradient U y) (gradient U x) ≤
                  (G : ℝ) * dist y x := hh
              _ ≤ (G : ℝ) * (φ k).rOut :=
                mul_le_mul_of_nonneg_left (le_of_lt hy') hG'
              _ = (G : ℝ) / ((k : ℝ) + 1) := by
                simp [φ, div_eq_mul_inv]
          exact hle)
    simpa [dist_eq_norm] using hdist
  · intro k
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hgrad k]
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
    have h₁ :
        Integrable
          (fun t : E =>
            (φ k).normed (volume : Measure E) t • gradient U (x - t))
          (volume : Measure E) := by
      apply integrable_smul_of_compact_support
      · exact (φ k).continuous_normed
      · exact (LipschitzWith.continuous hG).comp
          (continuous_const.sub continuous_id)
      · exact (φ k).hasCompactSupport_normed
    have h₂ :
        Integrable
          (fun t : E =>
            (φ k).normed (volume : Measure E) t • gradient U (y - t))
          (volume : Measure E) := by
      apply integrable_smul_of_compact_support
      · exact (φ k).continuous_normed
      · exact (LipschitzWith.continuous hG).comp
          (continuous_const.sub continuous_id)
      · exact (φ k).hasCompactSupport_normed
    rw [dist_eq_norm]
    have hsub :
        (∫ t : E, (φ k).normed (volume : Measure E) t • gradient U (x - t) ∂volume) -
            ∫ t : E, (φ k).normed (volume : Measure E) t • gradient U (y - t) ∂volume =
          ∫ t : E,
            ((φ k).normed (volume : Measure E) t • gradient U (x - t)) -
              ((φ k).normed (volume : Measure E) t • gradient U (y - t)) ∂volume :=
      (integral_sub h₁ h₂).symm
    rw [hsub]
    have hbound :
        Integrable
          (fun t : E =>
            (φ k).normed (volume : Measure E) t *
              ((G : ℝ) * ‖x - y‖))
          (volume : Measure E) := by
      apply integrable_mul_of_compact_support
      · exact (φ k).continuous_normed
      · exact continuous_const
      · exact (φ k).hasCompactSupport_normed
    have hnorm :
        ‖∫ t : E,
            ((φ k).normed (volume : Measure E) t • gradient U (x - t)) -
              ((φ k).normed (volume : Measure E) t • gradient U (y - t)) ∂volume‖ ≤
          ∫ t : E,
            (φ k).normed (volume : Measure E) t *
              ((G : ℝ) * ‖x - y‖) ∂volume := by
      apply norm_integral_le_of_norm_le hbound
      filter_upwards [] with t
      rw [← smul_sub, norm_smul]
      calc
        ‖(φ k).normed (volume : Measure E) t‖ *
              ‖gradient U (x - t) - gradient U (y - t)‖ ≤
            (φ k).normed (volume : Measure E) t *
              ((G : ℝ) * ‖x - y‖) := by
          rw [Real.norm_eq_abs, abs_of_nonneg ((φ k).nonneg_normed t)]
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [dist_eq_norm, sub_sub_sub_cancel_right] using
                hG.dist_le_mul (x - t) (y - t))
            ((φ k).nonneg_normed t)
        _ = (φ k).normed (volume : Measure E) t *
              ((G : ℝ) * ‖x - y‖) := rfl
    calc
      ‖∫ t : E,
          ((φ k).normed (volume : Measure E) t • gradient U (x - t)) -
            ((φ k).normed (volume : Measure E) t • gradient U (y - t)) ∂volume‖ ≤
          ∫ t : E,
            (φ k).normed (volume : Measure E) t *
              ((G : ℝ) * ‖x - y‖) ∂volume := hnorm
      _ = (G : ℝ) * dist x y := by
        have hrewrite :
            (fun t : E =>
              (φ k).normed (volume : Measure E) t *
                ((G : ℝ) * ‖x - y‖)) =
            (fun t : E =>
              ((G : ℝ) * ‖x - y‖) •
                (φ k).normed (volume : Measure E) t) := by
          funext t
          simp only [smul_eq_mul]
          ring
        rw [hrewrite, integral_smul]
        simp [dist_eq_norm, (φ k).integral_normed]
  · intro x
    have hcg :
        Tendsto
          (Function.uncurry (fun _ : ℕ => U))
          (atTop ×ˢ 𝓝 x) (𝓝 (U x)) := by
      change Tendsto (fun p : ℕ × E => U p.2)
        (atTop ×ˢ 𝓝 x) (𝓝 (U x))
      exact (hU.continuous.tendsto x).comp
        (tendsto_snd : Tendsto Prod.snd (atTop ×ˢ 𝓝 x) (𝓝 x))
    simpa [Uk] using
      ContDiffBump.convolution_tendsto_right
        (φ := φ) (g := fun _ : ℕ => U) (k := fun _ : ℕ => x)
        (x₀ := x) (z₀ := U x) hφ
        (by
          filter_upwards [] with k
          exact hU.continuous.aestronglyMeasurable)
        hcg tendsto_const_nhds
  · have hconv :
        ∀ k x,
          fderiv ℝ (gradient (Uk k)) x =
            convolution
              ((φ k).normed (volume : Measure E)) (fderiv ℝ (gradient U))
              (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E) x := by
      intro k x
      rw [hgrad k]
      simpa using
        (FunctionalInequalities.Analysis.hasFDerivAt_convolution_normed_of_lipschitz_408915f
          hG (φ k) x).fderiv
    filter_upwards [
      ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
        (φ := φ) (l := atTop) (K := 2) hφ hφ' hgradloc] with x hx
    simpa [hconv] using hx
