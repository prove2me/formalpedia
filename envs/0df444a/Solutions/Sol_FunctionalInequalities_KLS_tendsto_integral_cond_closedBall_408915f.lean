-- Prove2me | solution 1 for FunctionalInequalities.KLS.tendsto_integral_cond_closedBall_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:28:02.015997+00:00
-- url     : https://prove2.me/submissions/06f8141f-bd44-473d-bb74-207374fc1679

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory
section LT10ABallConditioningMoments
open MeasureTheory Set Metric Filter
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities.KLS in
/-- **Conditioning on a large ball preserves weak convergence** (Letwin Lemma A.1 approximation):
if `ν k → μ` weakly and `μ` is carried by `closedBall 0 r` with `r < R`, then for every continuous `f` the
integrals against the conditioned laws `ν k [| closedBall 0 R]` converge to `∫ f dμ`. -/
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ℕ → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E} (hν : Tendsto ν atTop (𝓝 μ)) {r R : ℝ} (hrR : r < R)
    (hsupp : (μ : Measure E) (closedBall (0 : E) r)ᶜ = 0) {f : E → ℝ} (hf : Continuous f) :
    Tendsto (fun k => ∫ x, f x ∂(ProbabilityTheory.cond (ν k : Measure E) (closedBall (0 : E) R)))
      atTop (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
  let B : Set E := closedBall (0 : E) R
  have hB : MeasurableSet B := isClosed_closedBall.measurableSet
  have hsub : closedBall (0 : E) r ⊆ B :=
    closedBall_subset_closedBall hrR.le
  have hBc : (μ : Measure E) Bᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hsub) hsupp
  have hBmass : (μ : Measure E) B = 1 := by
    simpa only [measure_univ] using measure_of_measure_compl_eq_zero hBc
  have hfront : (μ : Measure E) (frontier B) = 0 := by
    apply measure_mono_null (t := (closedBall (0 : E) r)ᶜ) _ hsupp
    intro x hx hxr
    have hxR : dist x 0 = R :=
      mem_sphere.mp (frontier_closedBall_subset_sphere hx)
    have hxr' : dist x 0 ≤ r := mem_closedBall.mp hxr
    linarith
  have hmass :
      Tendsto (fun k => (ν k : Measure E) B) atTop (𝓝 (1 : ENNReal)) := by
    rw [← hBmass]
    exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hν hfront
  have hcompl :
      Tendsto (fun k => (ν k : Measure E) Bᶜ) atTop (𝓝 (0 : ENNReal)) := by
    rw [← hBc]
    apply ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hν
    rw [frontier_compl]
    exact hfront
  have hmassReal :
      Tendsto (fun k => ((ν k : Measure E) B).toReal) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_one] using
      (ENNReal.tendsto_toReal (by simp : (1 : ENNReal) ≠ ⊤)).comp hmass
  have hcomplReal :
      Tendsto (fun k => ((ν k : Measure E) Bᶜ).toReal) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hcompl

  -- Clip the values of f to obtain a bounded continuous function equal to f on B.
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hf.continuousOn
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hfC : ∀ x ∈ B, ‖f x‖ ≤ C := by
    intro x hx
    exact (hC₀ x hx).trans (le_max_left _ _)
  have hclip : ∀ x : E, ‖max (-C) (min C (f x))‖ ≤ C := by
    intro x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  let g : BoundedContinuousFunction E ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => max (-C) (min C (f x)))
      (continuous_const.max (continuous_const.min hf)) C hclip
  have hg_eq : EqOn (fun x => g x) f B := by
    intro x hx
    change max (-C) (min C (f x)) = f x
    have hx' := abs_le.mp (show |f x| ≤ C from hfC x hx)
    rw [min_eq_right hx'.2, max_eq_right hx'.1]
  have hgμ : (∫ x, g x ∂(μ : Measure E)) = ∫ x, f x ∂(μ : Measure E) := by
    apply integral_congr_ae
    have hae : ∀ᵐ x ∂(μ : Measure E), x ∈ B := ae_iff.mpr hBc
    exact hae.mono fun x hx => hg_eq hx
  have hg :
      Tendsto (fun k => ∫ x, g x ∂(ν k : Measure E)) atTop
        (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
    rw [← hgμ]
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν g

  have htail :
      Tendsto (fun k => ∫ x in Bᶜ, g x ∂(ν k : Measure E)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm
      (a := fun k => ‖g‖ * ((ν k : Measure E) Bᶜ).toReal)
    · intro k
      have hbound :
          ‖∫ x in Bᶜ, g x ∂(ν k : Measure E)‖ ≤
            ‖g‖ * ((ν k : Measure E).restrict Bᶜ).real univ :=
        norm_integral_le_of_norm_le_const
          (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)
      simpa only [Measure.real_def, Measure.restrict_apply_univ] using hbound
    · simpa only [mul_zero] using
        (tendsto_const_nhds.mul hcomplReal :
          Tendsto (fun k => ‖g‖ * ((ν k : Measure E) Bᶜ).toReal)
            atTop (𝓝 (‖g‖ * 0)))
  have hrestricted :
      Tendsto (fun k => ∫ x in B, f x ∂(ν k : Measure E)) atTop
        (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
    have hlim := hg.sub htail
    rw [sub_zero] at hlim
    apply hlim.congr'
    apply Filter.Eventually.of_forall
    intro k
    have hsplit := integral_add_compl hB (g.integrable (ν k : Measure E))
    have heq :
        (∫ x in B, g x ∂(ν k : Measure E)) =
          ∫ x in B, f x ∂(ν k : Measure E) :=
      setIntegral_congr_fun hB hg_eq
    linarith
  have hinv :
      Tendsto (fun k => ((ν k : Measure E) B).toReal⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [inv_one] using hmassReal.inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)
  have hlim := hinv.mul hrestricted
  rw [one_mul] at hlim
  change Tendsto
    (fun k => ∫ x, f x ∂(((ν k : Measure E) B)⁻¹ • (ν k : Measure E).restrict B))
    atTop (𝓝 (∫ x, f x ∂(μ : Measure E)))
  simpa only [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul] using hlim
