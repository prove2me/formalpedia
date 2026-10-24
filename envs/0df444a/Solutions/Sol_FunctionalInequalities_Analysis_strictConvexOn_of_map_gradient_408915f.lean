-- Prove2me | solution 1 for FunctionalInequalities.Analysis.strictConvexOn_of_map_gradient_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:19:37.887412+00:00
-- url     : https://prove2.me/submissions/2e9d984b-b02d-4fc1-a110-c0f3c6eb1e12

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_eq_of_contact_of_sublevel_bounds_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_strictConvexOn_of_contact_eq_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradientImage_eq_lintegral_of_isOpen_408915f

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F6MomentStrictConvexity
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **The moment potential is strictly convex** (weak Letwin route; KLS500
`moment_strictConvexOn`): a convex Lipschitz `u` with `∫ e^{-u} = 1` whose gradient pushes `e^{-u} dx` forward
to `1_K e^{-V} dx` (`K` compact convex nonempty, `V` continuous) is strictly convex. -/
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    {V : E → ℝ} (hV : Continuous V)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p)))) :
    StrictConvexOn ℝ univ u := by
  classical
  let ρ : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-u x))
  let f : E → ℝ≥0∞ := K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))
  have hρ : Measurable ρ := hu.continuous.measurable.neg.exp.ennreal_ofReal
  have hf : Measurable f :=
    hV.measurable.neg.exp.ennreal_ofReal.indicator hK.measurableSet
  have hgrad : Measurable (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  have htilt : (volume : Measure E).tilted (-u) = volume.withDensity ρ := by
    change (volume : Measure E).withDensity
      (fun x => ENNReal.ofReal
        (Real.exp (-u x) / ∫ y, Real.exp (-u y) ∂(volume : Measure E))) =
      volume.withDensity ρ
    simp only [hnorm, div_one, ρ]
  have hmap' :
      ((volume : Measure E).withDensity ρ).map (gradient u) =
        volume.withDensity f := by
    rw [← htilt]
    exact hmap
  have hμK : ∀ᵐ p ∂(volume : Measure E).withDensity f, p ∈ K := by
    apply (ae_withDensity_iff hf).2
    exact Filter.Eventually.of_forall fun p hp => by
      by_contra h
      exact hp (Set.indicator_of_notMem h _)
  have hνK :
      ∀ᵐ x ∂(volume : Measure E).withDensity ρ, gradient u x ∈ K := by
    apply ae_of_ae_map hgrad.aemeasurable
    rw [hmap']
    exact hμK
  have hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K := by
    have h := (ae_withDensity_iff hρ).1 hνK
    filter_upwards [h] with x hx
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (-u x))))
  have hint : Integrable (fun x => Real.exp (-u x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; exact one_ne_zero)
  have hsub : ∀ R : ℝ, IsCompact {x | u x ≤ R} :=
    (FunctionalInequalities.Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_408915f
      volume hconv hint).2
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hV.continuousOn
  obtain ⟨q, hq⟩ := hKne
  have hDnonneg : 0 ≤ D := (norm_nonneg (V q)).trans (hD q hq)
  apply FunctionalInequalities.Analysis.strictConvexOn_of_contact_eq_408915f hconv
  intro x p hp y hy
  let R : ℝ := max (u x) (u y) + 1
  have hyR : u y < R := by
    dsimp only [R]
    linarith [le_max_right (u x) (u y)]
  refine FunctionalInequalities.Analysis.eq_of_contact_of_sublevel_bounds_408915f hconv hp (hsub R) ?_ hyR hy
  intro Q hQ _
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hu.continuous.continuousOn
  refine ⟨Real.exp (-C - D), Real.exp (C + D), Real.exp_pos _, ?_⟩
  intro G hG hGQ
  have hbounds :
      ∀ᵐ z ∂(volume : Measure E).restrict G,
        ENNReal.ofReal (Real.exp (-C - D)) ≤
            ENNReal.ofReal (Real.exp (-u z + V (gradient u z))) ∧
          ENNReal.ofReal (Real.exp (-u z + V (gradient u z))) ≤
            ENNReal.ofReal (Real.exp (C + D)) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hG.measurableSet]
      with z hzK hzG
    have hzQ : z ∈ Q := hGQ (subset_closure hzG)
    have huz : -C ≤ u z ∧ u z ≤ C := by
      apply abs_le.mp
      simpa only [Real.norm_eq_abs] using hC z hzQ
    have hvz : -D ≤ V (gradient u z) ∧ V (gradient u z) ≤ D := by
      apply abs_le.mp
      simpa only [Real.norm_eq_abs] using hD (gradient u z) hzK
    constructor
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith [huz.2, hvz.1]
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith [huz.1, hvz.2, hDnonneg]
  rw [FunctionalInequalities.Analysis.volume_subgradientImage_eq_lintegral_of_isOpen_408915f
    hu hconv hnorm hK.isClosed hKc hV.measurable hmap hG]
  constructor
  · calc
      ENNReal.ofReal (Real.exp (-C - D)) * (volume : Measure E) G =
          ∫⁻ z in G, ENNReal.ofReal (Real.exp (-C - D)) ∂(volume : Measure E) :=
        (setLIntegral_const G _).symm
      _ ≤ ∫⁻ z in G, ENNReal.ofReal (Real.exp (-u z + V (gradient u z)))
          ∂(volume : Measure E) :=
        lintegral_mono_ae (hbounds.mono fun _ hz => hz.1)
  · calc
      (∫⁻ z in G, ENNReal.ofReal (Real.exp (-u z + V (gradient u z)))
          ∂(volume : Measure E)) ≤
          ∫⁻ z in G, ENNReal.ofReal (Real.exp (C + D)) ∂(volume : Measure E) :=
        lintegral_mono_ae (hbounds.mono fun _ hz => hz.2)
      _ = ENNReal.ofReal (Real.exp (C + D)) * (volume : Measure E) G :=
        setLIntegral_const G _
