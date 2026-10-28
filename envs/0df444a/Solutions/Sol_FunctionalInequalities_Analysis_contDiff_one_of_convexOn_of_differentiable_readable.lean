-- Prove2me | solution 1 for FunctionalInequalities.Analysis.contDiff_one_of_convexOn_of_differentiable_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:30:33.491271+00:00
-- url     : https://prove2.me/submissions/0cb8c6d1-d71d-4e89-a972-bb22da27e2cc

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section ConvexC1
/-- **A differentiable convex function on a finite-dimensional space is `C¹`** (weak Letwin
route): convexity makes the derivative map continuous. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u) :
    ContDiff ℝ 1 u := by
  have hline (x w : E) :
      HasDerivAt (fun t : ℝ => u (x + t • w)) (fderiv ℝ u x w) 0 := by
    have hp : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    have hu : HasFDerivAt u (fderiv ℝ u x) (x + (0 : ℝ) • w) := by
      simpa only [zero_smul, add_zero] using (hdiff x).hasFDerivAt
    exact hu.comp_hasDerivAt 0 hp

  -- The supporting hyperplane inequality follows from convexity on each line.
  have hsupport (x y : E) :
      fderiv ℝ u x (y - x) ≤ u y - u x := by
    have hc : ConvexOn ℝ Set.univ
        (fun t : ℝ => u (x + t • (y - x))) := by
      simpa only [Set.preimage_univ, Function.comp_def,
        AffineMap.lineMap_apply_module', add_comm] using
        hconv.comp_affineMap (AffineMap.lineMap x y)
    simpa only [slope_def_field, zero_smul, add_zero, one_smul,
      add_sub_cancel, sub_zero, div_one] using
      hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
        zero_lt_one (hline x (y - x))

  have hbound (x w : E) (t : ℝ) (ht : 0 < t) :
      fderiv ℝ u x w ≤ (u (x + t • w) - u x) / t := by
    apply (le_div_iff₀ ht).2
    have h := hsupport x (x + t • w)
    simpa only [add_sub_cancel_left, map_smul, smul_eq_mul, mul_comm] using h

  -- For fixed direction, positive difference quotients give continuous upper bounds.
  have hupper (w x : E) (a : ℝ) (ha : fderiv ℝ u x w < a) :
      ∀ᶠ z in nhds x, fderiv ℝ u z w < a := by
    have hlim :
        Filter.Tendsto (fun t : ℝ => (u (x + t • w) - u x) / t)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (fderiv ℝ u x w)) := by
      simpa only [zero_add, zero_smul, add_zero, smul_eq_mul,
        div_eq_mul_inv, mul_comm] using
        (hline x w).tendsto_slope_zero.mono_left
          (nhdsGT_le_nhdsNE (0 : ℝ))
    have hev := (hlim.eventually_lt_const ha).and
      (self_mem_nhdsWithin :
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t)
    obtain ⟨t, ht, htpos⟩ := hev.exists
    have hc : Continuous (fun z : E => (u (z + t • w) - u z) / t) :=
      ((hdiff.continuous.comp (continuous_id.add continuous_const)).sub
        hdiff.continuous).div_const t
    exact (hc.continuousAt.eventually_lt continuousAt_const ht).mono
      (fun z hz => lt_of_le_of_lt (hbound z w t htpos) hz)

  -- Applying the upper bound to the negative direction also gives a lower bound.
  have heval (w : E) : Continuous (fun x => fderiv ℝ u x w) := by
    apply continuous_iff_continuousAt.2
    intro x
    apply tendsto_order.2
    constructor
    · intro a ha
      have hn : fderiv ℝ u x (-w) < -a := by
        simpa only [map_neg] using neg_lt_neg ha
      exact (hupper (-w) x (-a) hn).mono fun z hz => by
        simpa only [map_neg, neg_lt_neg_iff] using hz
    · intro a ha
      exact hupper w x a ha

  -- In finite dimension, continuity on a basis gives continuity in operator norm.
  apply contDiff_one_iff_fderiv.2
  refine ⟨hdiff, ?_⟩
  let b := Module.finBasis ℝ E
  let L : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ) :=
    (b.constr ℝ).trans LinearMap.toContinuousLinearMap
  have hL : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
  have heq (x : E) :
      L (fun i => fderiv ℝ u x (b i)) = fderiv ℝ u x := by
    apply ContinuousLinearMap.ext
    intro w
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f w)
      (b.constr_self ℝ (fderiv ℝ u x).toLinearMap)
  exact (hL.comp (continuous_pi (fun i => heval (b i)))).congr heq
