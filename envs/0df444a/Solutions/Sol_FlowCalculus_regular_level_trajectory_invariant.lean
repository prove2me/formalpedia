-- Prove2me | solution 1 for FlowCalculus.regular_level_trajectory_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T20:22:57.976107+00:00
-- url     : https://prove2.me/submissions/0913379c-8cf4-432f-9008-8a3f53ce799f

import Theorems.Thm_ImplicitCalculus_local_constraint_residual_bound
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

open Set Filter
open scoped Topology NNReal ContDiff
set_option autoImplicit false

theorem constraint_zero_of_residual_bound
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : V → W) (hF : Differentiable ℝ F)
    (X : ℝ → V → V) (γ : ℝ → V) (a b K : ℝ)
    (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivAt γ (X t (γ t)) t)
    (h0 : F (γ a) = 0)
    (hbound : ∀ t ∈ Ico a b,
      ‖fderiv ℝ F (γ t) (X t (γ t))‖ ≤ K * ‖F (γ t)‖) :
    ∀ t ∈ Icc a b, F (γ t) = 0 := by
  apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (hF.continuous.comp_continuousOn hc) _ h0 hbound
  intro t ht
  exact ((hF (γ t)).hasFDerivAt.comp_hasDerivAt t (hd t ht)).hasDerivWithinAt

theorem residual_bound_of_retraction
    {V W U : Type*} [PseudoMetricSpace V]
    [NormedAddCommGroup W] [NormedAddCommGroup U]
    (F : V → W) (H : V → U) (r : V → V) (s : Set V)
    (L C : ℝ≥0) (hL : LipschitzOnWith L H s)
    (hr : MapsTo r s s) (hzero : ∀ z ∈ s, H (r z) = 0)
    (hbound : ∀ z ∈ s, dist z (r z) ≤ C * ‖F z‖) :
    ∀ z ∈ s, ‖H z‖ ≤ (L * C : ℝ≥0) * ‖F z‖ := by
  intro z hz
  calc
    ‖H z‖ = dist (H z) (H (r z)) := by simp [hzero z hz, dist_zero_right]
    _ ≤ L * dist z (r z) := hL.dist_le_mul _ hz _ (hr hz)
    _ ≤ L * (C * ‖F z‖) := mul_le_mul_of_nonneg_left (hbound z hz) L.2
    _ = (L * C : ℝ≥0) * ‖F z‖ := by simp [mul_assoc]





open Set Filter
open scoped Topology NNReal
set_option autoImplicit false

theorem uniform_bound_on_compact_of_local_bound
    {A : Type*} [TopologicalSpace A] (S : Set A) (hS : IsCompact S)
    (f g : A → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hlocal : ∀ x ∈ S, ∃ C : ℝ≥0, ∀ᶠ z in 𝓝[S] x, g z ≤ C * f z) :
    ∃ C : ℝ≥0, ∀ z ∈ S, g z ≤ C * f z := by
  classical
  choose C hC using hlocal
  let U : ∀ x ∈ S, Set A := fun x hx => {z | g z ≤ C x hx * f z}
  obtain ⟨I, hI⟩ := hS.elim_nhdsWithin_subcover' U (fun x hx => hC x hx)
  let cS : S → ℝ≥0 := fun x => C x x.2
  refine ⟨∑ x ∈ I, cS x, ?_⟩
  intro z hz
  obtain ⟨x, hx, hzU⟩ := mem_iUnion₂.mp (hI hz)
  have hle : cS x ≤ ∑ i ∈ I, cS i :=
    Finset.single_le_sum (fun i _ => (show (0 : ℝ≥0) ≤ cS i from bot_le)) hx
  exact hzU.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast hle) (hf z))

open scoped ContDiff

theorem solution {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (F : V → W) (hF : ContDiff ℝ ∞ F)
    (hreg : ∀ y, F y = 0 → Function.Surjective (fderiv ℝ F y))
    (X : ℝ → V → V) (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (a b : ℝ) (htan : ∀ t ∈ Icc a b, ∀ y, F y = 0 → fderiv ℝ F y (X t y) = 0)
    (γ : ℝ → V) (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivAt γ (X t (γ t)) t)
    (h0 : F (γ a) = 0) : ∀ t ∈ Icc a b, F (γ t) = 0 := by
  let H : ℝ × V → W := fun p => fderiv ℝ F p.2 (X p.1 p.2)
  have hH : ContDiff ℝ ∞ H :=
    ((contDiff_infty_iff_fderiv.mp hF).2.comp contDiff_snd).clm_apply hX
  have hp : ContinuousOn (fun s => (s, γ s)) (Icc a b) := continuousOn_id.prodMk hc
  have hFc : ContinuousOn (fun s => ‖F (γ s)‖) (Icc a b) :=
    (hF.continuous.comp_continuousOn hc).norm
  have hHc : ContinuousOn (fun s => ‖H (s, γ s)‖) (Icc a b) :=
    (hH.continuous.comp_continuousOn hp).norm
  have hlocal : ∀ t ∈ Icc a b, ∃ C : ℝ≥0, ∀ᶠ s in 𝓝[Icc a b] t,
      ‖H (s, γ s)‖ ≤ C * ‖F (γ s)‖ := by
    intro t ht
    by_cases hz : F (γ t) = 0
    · obtain ⟨C, hC⟩ := ImplicitCalculus.local_constraint_residual_bound F (fderiv ℝ F (γ t)) (γ t)
        (hF.hasStrictFDerivAt (by simp)) (hreg (γ t) hz)
        H (fderiv ℝ H (t, γ t)) t (Icc a b)
        (hH.hasStrictFDerivAt (by simp)) (by
          intro s hs y hy
          exact htan s hs y (hy.trans hz))
      refine ⟨C, ?_⟩
      filter_upwards [(hp t ht).eventually hC, self_mem_nhdsWithin] with s hs hsI
      simpa [hz] using hs hsI
    · have hn : ‖F (γ t)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      have hr := (hHc t ht).div (hFc t ht) hn
      let C : ℝ≥0 := ⟨‖H (t, γ t)‖ / ‖F (γ t)‖ + 1, by positivity⟩
      have hlt : ‖H (t, γ t)‖ / ‖F (γ t)‖ < (C : ℝ) := by
        change ‖H (t, γ t)‖ / ‖F (γ t)‖ < ‖H (t, γ t)‖ / ‖F (γ t)‖ + 1
        linarith
      refine ⟨C, ?_⟩
      filter_upwards [hr.tendsto.eventually (eventually_lt_nhds hlt),
        (hFc t ht).tendsto.eventually (eventually_gt_nhds (norm_pos_iff.mpr hz))]
        with s hs hspos
      exact ((div_lt_iff₀ hspos).mp hs).le
  obtain ⟨C, hC⟩ := uniform_bound_on_compact_of_local_bound (Icc a b) isCompact_Icc
    (fun s => ‖F (γ s)‖) (fun s => ‖H (s, γ s)‖) (fun _ => norm_nonneg _) hlocal
  exact constraint_zero_of_residual_bound F (hF.differentiable (by simp)) X γ a b C
    hc hd h0 (fun t ht => hC t (Ico_subset_Icc_self ht))
