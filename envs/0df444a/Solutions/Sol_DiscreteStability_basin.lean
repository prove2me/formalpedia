-- Prove2me | solution 1 for DiscreteStability.basin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:30.015445+00:00
-- url     : https://prove2.me/submissions/e1ca8875-ebd6-4d84-9e98-bf43606aaed3

import Definitions.Def_DiscreteStability_Stability
import Definitions.Def_DiscreteStability_Basin
import Theorems.Thm_DiscreteStability_continuousOn_of_lip
import Theorems.Thm_DiscreteStability_segment_ge
import Theorems.Thm_DiscreteStability_step_strict
import Theorems.Thm_DiscreteStability_tendsto_of_weighted_ascent


set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → ℝ} {g : E → E} {xbar : E} {L Λ c η : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}
namespace DiscreteStability
theorem _root_.solution {U : Set E} (hU : IsOpen U) (hxU : xbar ∈ U) (hcomp : IsCompact (closure U))
    (hgrad : ∀ z ∈ closure U, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hL : 0 ≤ L) (hlip : ∀ u ∈ closure U, ∀ v ∈ closure U, ‖g u - g v‖ ≤ L * ‖u - v‖)
    (hc : ∀ y ∈ U, c < f y) (hM : ∀ y ∈ U, y ≠ xbar → f y < f xbar)
    (hH5 : ∀ y ∈ frontier U, f y = c) (hH6 : ∀ y ∈ closure U, y ≠ xbar → g y ≠ 0)
    (hP : ∀ k, StepBound (P k) (lo k) (hi k)) (hΛ : ∀ k, hi k ≤ Λ)
    (hη : 0 < η) (hS3 : L * Λ ≤ 2 - η)
    (hH3 : Tendsto (fun N => ∑ k ∈ Finset.range N, lo k) atTop atTop) :
    ∀ (k₀ : ℕ) (x : ℕ → E), IsOrbit P g k₀ x → x k₀ ∈ U →
      (∀ k ≥ k₀, x k ∈ U) ∧ Tendsto x atTop (𝓝 xbar) := by
  have hLhi : ∀ k, L * hi k ≤ 2 - η := fun k =>
    (mul_le_mul_of_nonneg_left (hΛ k) hL).trans hS3
  have hfront : ∀ y ∈ closure U, y ∉ U → y ∈ frontier U := fun y hy hyU => by
    rw [frontier, hU.interior_eq]; exact ⟨hy, hyU⟩
  /- Forward invariance: the whole segment `[y, y + P_k g y]` stays in `U`. -/
  have hseg : ∀ y ∈ U, ∀ k, ∀ s ∈ Icc (0 : ℝ) 1, y + s • P k (g y) ∈ U := by
    intro y hy k
    by_contra hcon
    push Not at hcon
    set d := P k (g y) with hd
    set l : ℝ → E := fun s => y + s • d with hl
    have hlc : Continuous l := continuous_const.add (continuous_id.smul continuous_const)
    set S := Icc (0 : ℝ) 1 ∩ l ⁻¹' Uᶜ with hS
    have hSc : IsClosed S := isClosed_Icc.inter (hU.isClosed_compl.preimage hlc)
    have hSne : S.Nonempty := by
      obtain ⟨s, hs, hsU⟩ := hcon
      exact ⟨s, hs, hsU⟩
    have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
    set s₀ := sInf S with hs₀
    have hs₀S : s₀ ∈ S := hSc.csInf_mem hSne hSbdd
    have hbefore : ∀ τ, 0 ≤ τ → τ < s₀ → l τ ∈ U := by
      intro τ hτ0 hτ
      by_contra hτU
      have : s₀ ≤ τ := csInf_le hSbdd ⟨⟨hτ0, hτ.le.trans hs₀S.1.2⟩, hτU⟩
      linarith
    have hs₀pos : 0 < s₀ := by
      rcases hs₀S.1.1.eq_or_lt with h | h
      · exfalso
        apply hs₀S.2
        show l s₀ ∈ U
        rw [← h]; simpa [hl] using hy
      · exact h
    -- the first exit point lies in `closure U`
    have hy₀ : l s₀ ∈ closure U := by
      have h1 : s₀ ∈ closure (Ico 0 s₀) := by
        rw [closure_Ico hs₀pos.ne]; exact ⟨hs₀pos.le, le_rfl⟩
      have h2 := (hlc.continuousWithinAt (s := Ico 0 s₀)).mem_closure_image h1
      refine closure_mono ?_ h2
      rintro _ ⟨τ, hτ, rfl⟩
      exact hbefore τ hτ.1 hτ.2
    have hsegc : ∀ τ ∈ Icc (0 : ℝ) s₀, y + τ • d ∈ closure U := by
      intro τ hτ
      rcases hτ.2.eq_or_lt with h | h
      · rw [h]; exact hy₀
      · exact subset_closure (hbefore τ hτ.1 h)
    -- along `[y, l s₀]`, `f` stays `≥ f y > c` (C3), contradicting H5 at the exit point
    have hge := segment_ge (hP k) hL (by linarith [hLhi k]) hs₀S.1.2 hsegc hgrad hlip s₀
      ⟨hs₀pos.le, le_rfl⟩
    have hval := hH5 _ (hfront _ hy₀ hs₀S.2)
    have := hc y hy
    simp only [hl] at hval
    linarith
  intro k₀ x hx hx0
  have hinU : ∀ k ≥ k₀, x k ∈ U := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hx0
    | succ k hk ih =>
      rw [hx k hk]
      simpa using hseg (x k) ih k 1 ⟨zero_le_one, le_rfl⟩
  refine ⟨hinU, ?_⟩
  -- convergence: (C2) on `closure U` and the argument of Theorem 5.1(ii)
  have hasc : ∀ k ≥ k₀, f (x k) + η / 2 * lo k * ‖g (x k)‖ ^ 2 ≤ f (x (k + 1)) := by
    intro k hk
    rw [hx k hk]
    exact step_strict (hP k) hL (hLhi k) hη.le
      (fun τ hτ => subset_closure (hseg (x k) (hinU k hk) k τ hτ)) hgrad hlip
  have hcM : c < f xbar := hc xbar hxU
  refine tendsto_of_weighted_ascent hcomp (subset_closure hxU)
    (fun z hz => (hgrad z hz).continuousAt.continuousWithinAt) (continuousOn_of_lip hL hlip)
    ?_ hH6 (w := fun k => η / 2 * lo k)
    (fun k => mul_nonneg (by linarith) (hP k).lo_nonneg) ?_
    (fun k hk => subset_closure (hinU k hk)) (fun k hk => by simpa [mul_assoc] using hasc k hk)
  · intro y hy hne
    by_cases hyU : y ∈ U
    · exact hM y hyU hne
    · rw [hH5 y (hfront y hy hyU)]; exact hcM
  · have h1 : Tendsto (fun N => η / 2 * ∑ k ∈ Finset.range N, lo k) atTop atTop :=
      hH3.const_mul_atTop (by linarith)
    refine h1.congr fun N => ?_
    rw [Finset.mul_sum]
end DiscreteStability
