-- Prove2me | solution 1 for FiniteEnergyPlane.norm_iteratedFDeriv_intervalIntegral_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-12T22:34:32.799987+00:00
-- url     : https://prove2.me/submissions/a77f776f-b82c-4bc1-8645-ca33ecb2203d

import Mathlib
import Definitions.Def_FiniteEnergyPlane_TubeFamily

open Metric Set Filter Topology MeasureTheory
open scoped ContDiff



/-!
# Q-N, layer 8 (local, NOT published; Mathlib only): derivatives of a parametric interval integral

For `F : H → ℝ → G` jointly `C^∞` with `H` finite-dimensional,
`iteratedFDeriv k (x ↦ ∫₀¹ F x t dt) = ∫₀¹ iteratedFDeriv k (F · t) dt`, hence a uniform bound
on the integrand's `k`-th derivative bounds the integral's.
-/


noncomputable section

namespace QN8

variable {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Derivatives of a partial map `x ↦ Φ (x, t)`. -/
lemma iteratedFDeriv_partial_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : H × E → G) (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) (x : H) (t : E) :
    iteratedFDeriv ℝ k (fun x => Φ (x, t)) x =
      (iteratedFDeriv ℝ k Φ (x, t)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ H E) := by
  have hfun : (fun x => Φ (x, t)) =
      (fun y => Φ ((0, t) + y)) ∘ (ContinuousLinearMap.inl ℝ H E) := by
    funext x; simp
  have hf : ContDiff ℝ ∞ (fun y : H × E => Φ ((0, t) + y)) :=
    hΦ.comp (contDiff_const.add contDiff_id)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf x (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_left]
  simp

variable {F : H → ℝ → G}

lemma continuous_iteratedFDeriv_partial (hF : ContDiff ℝ ∞ (Function.uncurry F)) (k : ℕ) :
    Continuous (fun p : H × ℝ => iteratedFDeriv ℝ k (fun x => F x p.2) p.1) := by
  have hc : Continuous (fun y : H × ℝ => iteratedFDeriv ℝ k (Function.uncurry F) y) :=
    hF.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  refine ((ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ H ℝ)).continuous.comp hc).congr fun p => ?_
  have := iteratedFDeriv_partial_left (Function.uncurry F) hF k p.1 p.2
  simp only [Function.uncurry_apply_pair] at this
  simp [Function.comp, this]

lemma contDiff_partial (hF : ContDiff ℝ ∞ (Function.uncurry F)) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => F x t) := by
  have : (fun x => F x t) = Function.uncurry F ∘ fun x => (x, t) := by funext x; rfl
  rw [this]; exact hF.comp (contDiff_id.prodMk contDiff_const)

/-- **Interchange.** -/
theorem iteratedFDeriv_intervalIntegral (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ∀ k : ℕ, (fun x => iteratedFDeriv ℝ k (fun x => ∫ t in (0 : ℝ)..1, F x t) x) =
      fun x => ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (fun x => F x t) x := by
  intro k
  induction k with
  | zero =>
    funext x
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp]
    exact ((continuousMultilinearCurryFin0 ℝ H G).symm.toLinearIsometry.intervalIntegral_comp_comm
      (fun t => F x t)).symm
  | succ k ih =>
    funext x
    have hpk := continuous_iteratedFDeriv_partial hF k
    have hpk1 := continuous_iteratedFDeriv_partial hF (k + 1)
    -- derivative of the integral of the `k`-th derivatives
    have hfd : ∀ (t : ℝ) (y : H), fderiv ℝ (iteratedFDeriv ℝ k (fun x => F x t)) y =
        continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => H) G
          (iteratedFDeriv ℝ (k + 1) (fun x => F x t) y) := by
      intro t y
      rw [congrFun (iteratedFDeriv_succ_eq_comp_left (𝕜 := ℝ) (f := fun x => F x t) (n := k)) y,
        Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
    obtain ⟨C, hC⟩ := (isCompact_closedBall x 1 |>.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1)))
      |>.exists_bound_of_continuousOn hpk1.continuousOn
    have hderiv : HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (fun x => F x t) y)
        (∫ t in (0 : ℝ)..1, fderiv ℝ (iteratedFDeriv ℝ k (fun x => F x t)) x) x := by
      refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
        (F := fun y t => iteratedFDeriv ℝ k (fun x => F x t) y)
        (F' := fun y t => fderiv ℝ (iteratedFDeriv ℝ k (fun x => F x t)) y)
        (bound := fun _ => C) (ball_mem_nhds x one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
      · exact Eventually.of_forall fun y =>
          (hpk.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · exact (hpk.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
      · have hm := (hpk1.comp (continuous_const.prodMk continuous_id (f := fun _ : ℝ => x))).aestronglyMeasurable
          (μ := volume.restrict (Set.uIoc (0 : ℝ) 1))
        have := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => H) G).continuous.comp_aestronglyMeasurable hm
        refine this.congr (Eventually.of_forall fun t => ?_)
        exact (hfd t x).symm
      · refine Eventually.of_forall fun t ht y hy => ?_
        rw [norm_fderiv_iteratedFDeriv]
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          rw [uIoc_of_le zero_le_one] at ht; exact Ioc_subset_Icc_self ht
        exact hC (y, t) ⟨ball_subset_closedBall hy, ht'⟩
      · refine Eventually.of_forall fun t _ y _ => ?_
        exact ((contDiff_partial hF t).differentiable_iteratedFDeriv (m := k)
          (by exact_mod_cast ENat.coe_lt_top k) y).hasFDerivAt
    have ih' : iteratedFDeriv ℝ k (fun x => ∫ t in (0 : ℝ)..1, F x t) =
        fun x => ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (fun x => F x t) x := ih
    have hcont : Continuous (fun t : ℝ => fderiv ℝ (iteratedFDeriv ℝ k (fun x => F x t)) x) := by
      rw [show (fun t : ℝ => fderiv ℝ (iteratedFDeriv ℝ k (fun x => F x t)) x) = fun t =>
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => H) G
            (iteratedFDeriv ℝ (k + 1) (fun x => F x t) x) from funext fun t => hfd t x]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => H) G).continuous.comp
        (hpk1.comp (continuous_const.prodMk continuous_id (f := fun _ : ℝ => x)))
    have hc1 : Continuous (fun t : ℝ => iteratedFDeriv ℝ (k + 1) (fun x => F x t) x) :=
      hpk1.comp (continuous_const.prodMk continuous_id (f := fun _ : ℝ => x))
    ext m
    rw [iteratedFDeriv_succ_apply_left, ih', hderiv.fderiv,
      ContinuousLinearMap.intervalIntegral_apply
        (Continuous.intervalIntegrable (u := fun t : ℝ =>
          fderiv ℝ (iteratedFDeriv ℝ k (fun x => F x t)) x) (by exact hcont) 0 1)]
    have hc2 : Continuous (fun t : ℝ => fderiv ℝ (iteratedFDeriv ℝ k (fun x => F x t)) x (m 0)) :=
      hcont.clm_apply continuous_const
    rw [← ContinuousMultilinearMap.apply_apply (𝕜 := ℝ),
      ← (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => H) G (Fin.tail m)).intervalIntegral_comp_comm
        (Continuous.intervalIntegrable (u := fun t : ℝ =>
          fderiv ℝ (iteratedFDeriv ℝ k (fun x => F x t)) x (m 0)) (by exact hc2) 0 1),
      ← ContinuousMultilinearMap.apply_apply (𝕜 := ℝ),
      ← (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (k + 1) => H) G m).intervalIntegral_comp_comm
        (hc1.intervalIntegrable 0 1)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [ContinuousMultilinearMap.apply_apply]
    rw [iteratedFDeriv_succ_apply_left]

/-- **Bound.** -/
theorem norm_iteratedFDeriv_intervalIntegral_le (hF : ContDiff ℝ ∞ (Function.uncurry F)) (k : ℕ)
    (x : H) (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ k (fun x => F x t) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun x => ∫ t in (0 : ℝ)..1, F x t) x‖ ≤ C := by
  have := congrFun (iteratedFDeriv_intervalIntegral hF k) x
  rw [this]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t => iteratedFDeriv ℝ k (fun x => F x t) x) (C := C) (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht; exact hC t (Ioc_subset_Icc_self ht))
  simpa using h

end QN8

open FiniteEnergyPlane

theorem solution {H G : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {F : H → ℝ → G} (hF : ContDiff ℝ ∞ (Function.uncurry F)) (k : ℕ)
    (x : H) (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ k (fun x => F x t) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun x => ∫ t in (0 : ℝ)..1, F x t) x‖ ≤ C :=
  QN8.norm_iteratedFDeriv_intervalIntegral_le hF k x C hC
