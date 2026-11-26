-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma3_ball_image_of_deriv_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:14.932228+00:00
-- url     : https://prove2.me/submissions/960dd49d-c624-41d6-97d5-07400fd7675b

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma3_isOpen_image
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma3_hasDerivAt_invFunOn
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {g : ℂ → ℂ} {b : ℂ} {r m : ℝ}
    (hr : 0 < r) (hm : 0 ≤ m)
    (hgc : ContinuousOn g (closedBall b r))
    (hg : DifferentiableOn ℂ g (ball b r))
    (hinj : Set.InjOn g (ball b r))
    (hderiv : ∀ z ∈ ball b r, m ≤ ‖deriv g z‖) :
    ball (g b) (r * m) ⊆ g '' ball b r := by
  rcases eq_or_lt_of_le hm with hm0 | hmpos
  · rw [← hm0, mul_zero, Metric.ball_zero]
    exact Set.empty_subset _
  set A : Set ℂ := g '' ball b r with hA
  set h : ℂ → ℂ := Function.invFunOn g (ball b r) with hh
  have hne : ∀ z ∈ ball b r, deriv g z ≠ 0 := by
    intro z hz hcontra
    have := hderiv z hz
    rw [hcontra, norm_zero] at this
    linarith
  have hAopen : IsOpen A := lemma3_isOpen_image hg hinj
  have hbmem : g b ∈ A := ⟨b, Metric.mem_ball_self hr, rfl⟩
  have hhb : h (g b) = b := by
    have hex : ∃ a ∈ ball b r, g a = g b := ⟨b, Metric.mem_ball_self hr, rfl⟩
    exact hinj (Function.invFunOn_mem hex) (Metric.mem_ball_self hr) (Function.invFunOn_eq hex)
  -- the complement of the image is non-empty, because `g` is bounded on the closed ball
  have hAcne : (Aᶜ).Nonempty := by
    have hcomp : IsCompact (g '' closedBall b r) :=
      (isCompact_closedBall b r).image_of_continuousOn hgc
    obtain ⟨R, hR⟩ := hcomp.isBounded.subset_closedBall (g b)
    refine ⟨g b + ((|R| + 1 : ℝ) : ℂ), ?_⟩
    intro hmem
    have hsub : A ⊆ g '' closedBall b r :=
      Set.image_mono Metric.ball_subset_closedBall
    have := hR (hsub hmem)
    rw [Metric.mem_closedBall] at this
    simp only [dist_self_add_left, Complex.norm_real, Real.norm_eq_abs] at this
    rw [abs_of_pos (by positivity)] at this
    cases abs_cases R with
    | inl hc => linarith [hc.1]
    | inr hc => linarith [hc.1]
  have hAcclosed : IsClosed (Aᶜ) := hAopen.isClosed_compl
  set t : ℝ := Metric.infDist (g b) (Aᶜ) with hT
  have ht : 0 < t := by
    refine (Metric.infDist_pos_iff_notMem_closure hAcne).mp ?_
    rw [hAcclosed.closure_eq]
    simpa using hbmem
  have hballsub : ball (g b) t ⊆ A := by
    intro w hw
    by_contra hwA
    have hle : t ≤ dist (g b) w := Metric.infDist_le_dist_of_mem hwA
    rw [Metric.mem_ball, dist_comm] at hw
    linarith
  -- if the closest complement point is far enough away we are done
  by_cases hcase : r * m ≤ t
  · exact fun w hw => hballsub (Metric.ball_subset_ball hcase hw)
  -- otherwise derive a contradiction
  push Not at hcase
  exfalso
  obtain ⟨c, hcA, hcdist⟩ := hAcclosed.exists_infDist_eq_dist hAcne (g b)
  -- the inverse is `1/m`-Lipschitz on the convex set `ball (g b) t`
  have hlip : ∀ w ∈ ball (g b) t, dist (h w) b ≤ dist w (g b) / m := by
    intro w hw
    have hder : ∀ v ∈ ball (g b) t,
        HasFDerivWithinAt h
          (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv g (h v))⁻¹)
          (ball (g b) t) v := fun v hv =>
      ((lemma3_hasDerivAt_invFunOn hg hinj hne (hballsub hv)).hasFDerivAt).hasFDerivWithinAt
    have hbound : ∀ v ∈ ball (g b) t,
        ‖ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          (deriv g (h v))⁻¹‖ ≤ 1 / m := by
      intro v hv
      have hmem : h v ∈ ball b r := Function.invFunOn_mem (hballsub hv)
      have hb := hderiv _ hmem
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_inv, norm_one, one_mul, one_div]
      gcongr
    have := (convex_ball (g b) t).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hder hbound (Metric.mem_ball_self ht) hw
    rw [hhb] at this
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖h w - b‖ ≤ 1 / m * ‖w - g b‖ := this
      _ = ‖w - g b‖ / m := by ring
  -- `c` is a limit of image points inside `ball (g b) t`
  have hcclosure : c ∈ closure (ball (g b) t) := by
    rw [closure_ball _ (ne_of_gt ht)]
    rw [Metric.mem_closedBall, dist_comm]
    exact le_of_eq hcdist.symm
  obtain ⟨w, hwmem, hwlim⟩ := mem_closure_iff_seq_limit.mp hcclosure
  -- their preimages live in a compact sub-ball
  have hzmem : ∀ n, h (w n) ∈ closedBall b (t / m) := by
    intro n
    rw [Metric.mem_closedBall]
    have := hlip (w n) (hwmem n)
    have hd : dist (w n) (g b) < t := by simpa [Metric.mem_ball] using hwmem n
    calc dist (h (w n)) b ≤ dist (w n) (g b) / m := this
      _ ≤ t / m := by gcongr
  have hsub : closedBall b (t / m) ⊆ ball b r := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    have : t / m < r := by
      rw [div_lt_iff₀ hmpos]
      linarith [hcase]
    linarith
  obtain ⟨zstar, hzstar, φ, hφ, hlim⟩ :=
    (isCompact_closedBall b (t / m)).tendsto_subseq hzmem
  have hzstarmem : zstar ∈ ball b r := hsub hzstar
  -- the limit maps to `c`, contradicting `c ∉ A`
  have hgcont : ContinuousAt g zstar :=
    hg.continuousOn.continuousAt (isOpen_ball.mem_nhds hzstarmem)
  have hlim1 : Filter.Tendsto (fun n => g (h (w (φ n)))) Filter.atTop (𝓝 (g zstar)) :=
    hgcont.tendsto.comp hlim
  have heq : ∀ n, g (h (w (φ n))) = w (φ n) := fun n =>
    Function.invFunOn_eq (hballsub (hwmem (φ n)))
  have hlim2 : Filter.Tendsto (fun n => g (h (w (φ n)))) Filter.atTop (𝓝 c) := by
    simp only [heq]
    exact hwlim.comp hφ.tendsto_atTop
  have : g zstar = c := tendsto_nhds_unique hlim1 hlim2
  exact hcA ⟨zstar, hzstarmem, this⟩
end ExponentialJuliaSetMisiurewicz
