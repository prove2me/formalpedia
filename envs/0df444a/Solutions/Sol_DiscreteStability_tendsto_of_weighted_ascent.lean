-- Prove2me | solution 1 for DiscreteStability.tendsto_of_weighted_ascent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:43:26.43433+00:00
-- url     : https://prove2.me/submissions/32cb5683-565d-4ebb-a9b9-53f563e87bcb

import Definitions.Def_DiscreteStability_Ascent
import Definitions.Def_DiscreteStability_Stability
import Theorems.Thm_DiscreteStability_exists_pos_lower_bound


set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}
variable [FiniteDimensional ℝ E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace DiscreteStability
theorem _root_.solution {T : Set E} (hT : IsCompact T) (hxbarT : xbar ∈ T)
    (hf : ContinuousOn f T) (hg : ContinuousOn g T)
    (hflt : ∀ y ∈ T, y ≠ xbar → f y < f xbar) (hgne : ∀ y ∈ T, y ≠ xbar → g y ≠ 0)
    {w : ℕ → ℝ} (hw0 : ∀ k, 0 ≤ w k)
    (hw : Tendsto (fun N => ∑ k ∈ Finset.range N, w k) atTop atTop)
    {x : ℕ → E} {k₀ : ℕ} (hxT : ∀ k ≥ k₀, x k ∈ T)
    (hasc : ∀ k ≥ k₀, f (x k) + w k * ‖g (x k)‖ ^ 2 ≤ f (x (k + 1))) :
    Tendsto x atTop (𝓝 xbar) := by
  set v : ℕ → ℝ := fun k => f xbar - f (x k) with hvdef
  have hfle : ∀ y ∈ T, f y ≤ f xbar := by
    intro y hy
    by_cases h : y = xbar
    · rw [h]
    · exact (hflt y hy h).le
  have hv0 : ∀ k ≥ k₀, 0 ≤ v k := fun k hk => by
    simp only [hvdef]; linarith [hfle _ (hxT k hk)]
  have hvstep : ∀ k ≥ k₀, v (k + 1) ≤ v k - w k * ‖g (x k)‖ ^ 2 := fun k hk => by
    simp only [hvdef]; linarith [hasc k hk]
  have hvanti : ∀ k ≥ k₀, ∀ n ≥ k, v n ≤ v k := by
    intro k hk n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      have := hvstep n (hk.trans hn)
      have := mul_nonneg (hw0 n) (sq_nonneg ‖g (x n)‖)
      linarith
  -- `V_k` gets arbitrarily small
  have hsmall : ∀ c > 0, ∃ k ≥ k₀, v k < c := by
    intro c hc
    by_contra hcon
    push Not at hcon
    obtain ⟨δ₁, hδ₁, hδ₁f⟩ := Metric.continuousWithinAt_iff.mp (hf xbar hxbarT) c hc
    have hfar : ∀ k ≥ k₀, δ₁ ≤ dist (x k) xbar := by
      intro k hk
      by_contra h
      push Not at h
      have := hδ₁f (hxT k hk) h
      rw [Real.dist_eq] at this
      have := hcon k hk
      simp only [hvdef] at this
      linarith [neg_abs_le (f (x k) - f xbar)]
    have hK : IsCompact (T \ ball xbar δ₁) := hT.diff isOpen_ball
    have hgc : ContinuousOn (fun y => ‖g y‖ ^ 2) (T \ ball xbar δ₁) :=
      ((hg.mono sdiff_subset).norm).pow 2
    have hgpos : ∀ y ∈ T \ ball xbar δ₁, 0 < ‖g y‖ ^ 2 := by
      intro y hy
      have hne : y ≠ xbar := fun h => hy.2 (h ▸ mem_ball_self hδ₁)
      have := norm_pos_iff.mpr (hgne y hy.1 hne)
      positivity
    obtain ⟨m₁, hm₁, hm₁K⟩ := exists_pos_lower_bound hK hgc hgpos
    have hdesc : ∀ N, v (k₀ + N) ≤ v k₀ - m₁ * ∑ j ∈ Finset.range N, w (k₀ + j) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        have hk : k₀ + N ≥ k₀ := Nat.le_add_right _ _
        have h1 := hvstep (k₀ + N) hk
        have h2 : m₁ ≤ ‖g (x (k₀ + N))‖ ^ 2 :=
          hm₁K _ ⟨hxT _ hk, fun h => by
            have := hfar _ hk; rw [mem_ball] at h; linarith⟩
        have h3 := mul_le_mul_of_nonneg_left h2 (hw0 (k₀ + N))
        rw [Finset.sum_range_succ, ← add_assoc]
        nlinarith [h1, h3, ih]
    have hshift : Tendsto (fun N => ∑ j ∈ Finset.range N, w (k₀ + j)) atTop atTop := by
      refine (Filter.tendsto_atTop_add_const_right _ (-(∑ k ∈ Finset.range k₀, w k))
        (hw.comp (Filter.tendsto_add_atTop_nat k₀))).congr ?_
      intro N
      simp only [Function.comp_apply]
      rw [Nat.add_comm N k₀, Finset.sum_range_add]
      ring
    obtain ⟨N, hN⟩ := (hshift.eventually_gt_atTop (v k₀ / m₁)).exists
    rw [div_lt_iff₀ hm₁] at hN
    have := hdesc N
    have := hv0 (k₀ + N) (Nat.le_add_right _ _)
    nlinarith
  -- conclude `x k → x̄`
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hK : IsCompact (T \ ball xbar ε) := hT.diff isOpen_ball
  have hVc : ContinuousOn (fun y => f xbar - f y) (T \ ball xbar ε) :=
    continuousOn_const.sub (hf.mono sdiff_subset)
  have hVpos : ∀ y ∈ T \ ball xbar ε, 0 < f xbar - f y := by
    intro y hy
    have hne : y ≠ xbar := fun h => hy.2 (h ▸ mem_ball_self hε)
    linarith [hflt y hy.1 hne]
  obtain ⟨m', hm', hm'K⟩ := exists_pos_lower_bound hK hVc hVpos
  obtain ⟨k₁, hk₁, hvk₁⟩ := hsmall m' hm'
  refine ⟨k₁, fun n hn => ?_⟩
  by_contra hcon
  have hmem : x n ∈ T \ ball xbar ε := ⟨hxT n (hk₁.trans hn), fun h => hcon (mem_ball.mp h)⟩
  have := hm'K _ hmem
  have := hvanti k₁ hk₁ n hn
  simp only [hvdef] at *
  linarith
end DiscreteStability
