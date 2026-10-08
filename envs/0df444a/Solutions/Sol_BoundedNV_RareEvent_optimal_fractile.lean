-- Prove2me | solution 1 for BoundedNV.RareEvent.optimal_fractile
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:35:42.556237+00:00
-- url     : https://prove2.me/submissions/60561544-b77b-4e41-b31b-166097886709

import Mathlib
import Definitions.Def_BoundedNV_RareEvent_Logit
open MeasureTheory Filter Set
open scoped Topology
open BoundedNV.Uniform

private lemma min_integrable (f : ℝ → ℝ) (hf : BoundedNV.ExpFam.IsDemandDensity f) (x : ℝ) :
    Integrable (fun t => min t x * f t) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => min t x * f t) :=
    (continuous_id.min continuous_const).aestronglyMeasurable.mul hf.integrable.aestronglyMeasurable
  apply (hf.integrable.const_mul |x|).mono' hm
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.nonneg t)]
  by_cases ht : t < 0
  · simp [hf.zero_of_neg t ht]
  · apply mul_le_mul_of_nonneg_right _ (hf.nonneg t)
    rw [abs_le]
    constructor
    · apply le_min
      · have := neg_abs_le x; have := abs_nonneg x; linarith
      · exact neg_abs_le x
    · exact (min_le_right t x).trans (le_abs_self x)

private lemma min_derivative (f : ℝ → ℝ) (hf : BoundedNV.ExpFam.IsDemandDensity f) (m : ℝ) :
    HasDerivAt (expMin f) (1-demandCDF f m) m := by
  let F : ℝ → ℝ → ℝ := fun x t => min t x * f t
  let F' : ℝ → ℝ := (Ioi m).indicator f
  have hmeas : ∀ᶠ x in 𝓝 m, AEStronglyMeasurable (F x) := by
    filter_upwards [] with x
    exact (min_integrable f hf x).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable F' :=
    hf.integrable.aestronglyMeasurable.indicator measurableSet_Ioi
  have hlip : ∀ᵐ t : ℝ, LipschitzOnWith (Real.nnabs (f t)) (F · t) univ := by
    filter_upwards [] with t
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (LipschitzWith.id.const_min t).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    simpa only [F, Real.dist_eq, Real.coe_nnabs, ← sub_mul, ← mul_sub, abs_mul,
      id_eq, mul_comm] using
      mul_le_mul_of_nonneg_right h (abs_nonneg (f t))
  have hd : ∀ᵐ t : ℝ, HasDerivAt (F · t) (F' t) m := by
    filter_upwards [volume.ae_ne m] with t ht
    rcases lt_or_gt_of_ne ht with ht | ht
    · have he : (fun x => F x t) =ᶠ[𝓝 m] (fun _ => t*f t) := by
        filter_upwards [eventually_gt_nhds ht] with x hx
        simp [F, min_eq_left hx.le]
      have h := (hasDerivAt_const m (t*f t)).congr_of_eventuallyEq he
      simpa [F', mem_Ioi, not_lt.mpr ht.le] using h
    · have he : (fun x => F x t) =ᶠ[𝓝 m] (fun x => x*f t) := by
        filter_upwards [eventually_lt_nhds ht] with x hx
        simp [F, min_eq_right hx.le]
      have h := ((hasDerivAt_id m).mul_const (f t)).congr_of_eventuallyEq he
      simpa [F', mem_Ioi, ht] using h
  have h := (hasDerivAt_integral_of_dominated_loc_of_lip
    (bound := f) (F := F) (F' := F') (s := univ)
    (Filter.univ_mem) hmeas (min_integrable f hf m) hmeas' hlip hf.integrable hd).2
  have hi : ∫ t, F' t = 1-demandCDF f m := by
    rw [integral_indicator measurableSet_Ioi]
    have hh := integral_add_compl (s := Iic m) measurableSet_Iic hf.integrable
    rw [compl_Iic, hf.integral_eq_one] at hh
    unfold demandCDF
    linarith
  rw [hi] at h
  exact h

open BoundedNV.RareEvent

/-- The first step in the proof of Proposition 4, p. 586. -/
theorem solution (f : ℝ → ℝ) (p c m : ℝ)
    (hf : BoundedNV.ExpFam.IsDemandDensity f) (hp : 0 < p)
    (hm : IsMaxOn (BoundedNV.Uniform.nvProfit f p c) Set.univ m) :
    c = p * (1 - BoundedNV.Uniform.demandCDF f m) := by


  have hd := (min_derivative f hf m).const_mul p
  have hd' := hd.sub ((hasDerivAt_id m).const_mul c)
  have hz := (hm.isLocalMax (Filter.univ_mem)).hasDerivAt_eq_zero hd'
  linarith
#print axioms solution
