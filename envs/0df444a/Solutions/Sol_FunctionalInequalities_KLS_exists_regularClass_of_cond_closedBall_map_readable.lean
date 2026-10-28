-- Prove2me | solution 1 for FunctionalInequalities.KLS.exists_regularClass_of_cond_closedBall_map_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:38:46.885983+00:00
-- url     : https://prove2.me/submissions/17f61757-30f0-4749-8a37-60ba1b769cfe

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BallConditioning
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_readable
import Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_law_comp_affine_readable

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section
variable {V : E → ℝ} {a b : ℝ}
/-- The normalizing constant is positive. -/
theorem FunctionalInequalities.KLS.RegularPotential.integral_exp_neg_pos (hV : RegularPotential V a b) :
    0 < ∫ x, Real.exp ((-V) x) ∂(volume : Measure E) := by
    apply integral_exp_pos
    exact integrable_exp_neg hV
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
end
end
end
end

noncomputable section
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff
private theorem FunctionalInequalities.KLS.letwin_cond_map_equiv
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (e : A ≃ᵐ B) (S : Set A) (hS : MeasurableSet S) :
    (ProbabilityTheory.cond μ S).map e =
      ProbabilityTheory.cond (μ.map e) (e '' S) := by
  have hpre : e ⁻¹' (e '' S) = S :=
    Set.preimage_image_eq S e.injective
  have hm : (μ.map e) (e '' S) = μ S := by
    rw [Measure.map_apply e.measurable (e.measurableSet_image.mpr hS), hpre]
  rw [ProbabilityTheory.cond, Measure.map_smul, ProbabilityTheory.cond, hm,
    e.measurableEmbedding.restrict_map, hpre]
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private theorem FunctionalInequalities.KLS.letwin_cond_density
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {V : E → ℝ} {a b : ℝ} (hV : RegularPotential V a b)
    (S : Set E) (hS : MeasurableSet S) (h0 : (hV.law : Measure E) S ≠ 0) :
    ProbabilityTheory.cond (hV.law : Measure E) S =
      volume.withDensity
        (S.indicator fun x =>
          ENNReal.ofReal
            (Real.exp
              (-(V x + Real.log
                ((∫ y, Real.exp (-V y) ∂(volume : Measure E)) *
                  ((hV.law : Measure E) S).toReal))))) := by
  let Z : ℝ := ∫ x, Real.exp (-V x) ∂(volume : Measure E)
  let m : ℝ := ((hV.law : Measure E) S).toReal
  have hZ : 0 < Z := hV.integral_exp_neg_pos
  have hm : 0 < m :=
    ENNReal.toReal_pos h0 (measure_ne_top _ _)
  have hi : ENNReal.ofReal m⁻¹ = ((hV.law : Measure E) S)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hm,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hd : Measurable (fun x => ENNReal.ofReal (Real.exp (-V x) / Z)) :=
    (hV.temperate.1.continuous.neg.measurable.exp.div_const Z).ennreal_ofReal
  change
    ((hV.law : Measure E) S)⁻¹ •
      ((volume.withDensity
        (fun x => ENNReal.ofReal (Real.exp (-V x) / Z))).restrict S) = _
  rw [restrict_withDensity hS, ← withDensity_smul _ hd, withDensity_indicator hS]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change
    ((hV.law : Measure E) S)⁻¹ * ENNReal.ofReal (Real.exp (-V x) / Z) =
      ENNReal.ofReal (Real.exp (-(V x + Real.log (Z * m))))
  rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (Z * m)),
    Real.exp_log (mul_pos hZ hm)]
  have he :
      Real.exp (-V x) * (Z * m)⁻¹ =
        m⁻¹ * (Real.exp (-V x) / Z) := by
    simp only [mul_inv, div_eq_mul_inv]
    ring
  rw [he, ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), hi]
private theorem FunctionalInequalities.KLS.letwin_convex_sub_quadratic
    {f : E → ℝ} {a : ℝ} (hf : ContDiff ℝ 2 f)
    (h : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ f x v v) :
    ConvexOn ℝ univ (fun y => f y - (a / 2) * ‖y‖ ^ 2) := by
  have hc : ConvexOn ℝ univ (fun y => f y + (-a) / 2 * ‖y‖ ^ 2) := by
    apply Analysis.BakryEmery.convexOn_of_hessian_ge_readable
      (hf.add (contDiff_const.mul (contDiff_norm_sq ℝ))) (ρ := 0) le_rfl
    intro x v
    rw [Analysis.BakryEmery.bilinearIteratedFDerivTwo_add_quadratic hf]
    have hh := h x v
    nlinarith
  simpa only [neg_div, neg_mul, ← sub_eq_add_neg] using hc
/-- **Ball-conditioned, affinely transported regular laws lie in Letwin's class** (Letwin Lemma A.1):
conditioning the law of a regular potential `V` on `closedBall 0 R` (`R > 0`) and pushing forward by
`x ↦ L (x − c)` gives `1_K e^{−W} dx` with `K` compact convex with nonempty interior and `W` smooth and uniformly
convex. -/
theorem solution [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {V : E → ℝ} {a b : ℝ} (hV : FunctionalInequalities.KLS.RegularPotential V a b) {R : ℝ} (hR : 0 < R) (L : E ≃L[ℝ] E)
    (c : E) :
    ∃ (K : Set E) (W : E → ℝ) (κ : ℝ), 0 < κ ∧ IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
      ContDiff ℝ ∞ W ∧ ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) ∧
      (ProbabilityTheory.cond (hV.law : Measure E) (closedBall (0 : E) R)).map (fun x => L (x - c)) =
        (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) := by
  let H : E ≃ₜ E := (Homeomorph.addRight (-c)).trans L.toHomeomorph
  let e : E ≃ᵐ E := H.toMeasurableEquiv
  let K : Set E := e '' closedBall (0 : E) R
  have he : (e : E → E) = fun x => L (x - c) := by
    funext x
    change L (x + -c) = L (x - c)
    rw [sub_eq_add_neg]
  have hKcompact : IsCompact K := by
    change IsCompact (H '' closedBall (0 : E) R)
    exact (isCompact_closedBall (0 : E) R).image H.continuous
  have hKconvex : Convex ℝ K := by
    have heq :
        K = L '' ((fun x => -c + x) '' closedBall (0 : E) R) := by
      change e '' closedBall (0 : E) R =
        L '' ((fun x => -c + x) '' closedBall (0 : E) R)
      rw [Set.image_image]
      congr 1
      funext x
      rw [he]
      change L (x - c) = L (-c + x)
      rw [sub_eq_add_neg, add_comm]
    rw [heq]
    exact ((convex_closedBall (0 : E) R).translate (-c)).linear_image
      (L : E →ₗ[ℝ] E)
  have hKinterior : (interior K).Nonempty := by
    change (interior (H '' closedBall (0 : E) R)).Nonempty
    rw [← H.image_interior]
    exact ⟨H 0, Set.mem_image_of_mem H
      (mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds (0 : E) hR))⟩
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  let U : E → ℝ := fun y => V (L.symm y + c)
  let κ : ℝ := FunctionalInequalities.KLS.RegularPotential.affineLowerConstant a L.symm
  have hU : FunctionalInequalities.KLS.RegularPotential U κ
      (FunctionalInequalities.KLS.RegularPotential.affineUpperConstant b L.symm) :=
    hV.comp_affine L.symm c
  have hmap : (hV.law : Measure E).map e = (hU.law : Measure E) := by
    rw [he]
    simpa only [ContinuousLinearEquiv.symm_symm] using
      (hV.law_comp_affine_readable L.symm c).symm
  have hK0 : (hU.law : Measure E) K ≠ 0 := by
    obtain ⟨y, hy⟩ := hKinterior
    have hpos : 0 < (volume : Measure E) K :=
      Measure.measure_pos_of_mem_nhds volume (mem_interior_iff_mem_nhds.mp hy)
    intro hz
    exact (ne_of_gt hpos) (absolutelyContinuous_tilted hU.integrable_exp_neg hz)
  let d : ℝ :=
    Real.log
      ((∫ y, Real.exp (-U y) ∂(volume : Measure E)) *
        ((hU.law : Measure E) K).toReal)
  let W : E → ℝ := fun y => U y + d
  have hW : ContDiff ℝ ∞ W := hU.temperate.1.add contDiff_const
  have hconv : ConvexOn ℝ univ (fun y => U y - (κ / 2) * ‖y‖ ^ 2) :=
    FunctionalInequalities.KLS.letwin_convex_sub_quadratic
      (hU.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)) hU.lower
  have hWconv : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) := by
    have hh := hconv.add_const d
    change ConvexOn ℝ univ (fun y => (U y - (κ / 2) * ‖y‖ ^ 2) + d) at hh
    have heq :
        (fun y => W y - (κ / 2) * ‖y‖ ^ 2) =
          (fun y => (U y - (κ / 2) * ‖y‖ ^ 2) + d) := by
      funext y
      dsimp only [W]
      ring
    rw [heq]
    exact hh
  refine ⟨K, W, κ, hU.pos, hKcompact, hKconvex, hKinterior, hW, hWconv, ?_⟩
  calc
    (ProbabilityTheory.cond (hV.law : Measure E) (closedBall (0 : E) R)).map
        (fun x => L (x - c)) =
      (ProbabilityTheory.cond (hV.law : Measure E) (closedBall (0 : E) R)).map e := by
        rw [he]
    _ = ProbabilityTheory.cond ((hV.law : Measure E).map e) K :=
      FunctionalInequalities.KLS.letwin_cond_map_equiv (hV.law : Measure E) e
        (closedBall (0 : E) R) measurableSet_closedBall
    _ = ProbabilityTheory.cond (hU.law : Measure E) K := by rw [hmap]
    _ = (volume : Measure E).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) :=
      FunctionalInequalities.KLS.letwin_cond_density hU K hKmeas hK0
