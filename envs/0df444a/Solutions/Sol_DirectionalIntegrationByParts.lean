-- Prove2me | solution 1 for DirectionalIntegrationByParts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:13:48.095988+00:00
-- url     : https://prove2.me/submissions/6c5be407-451c-41fd-8b42-1ff93169c8ae

import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral
import Definitions.Def_PHigherOrder_DirectionalIntegrationByParts
import Theorems.Thm_TestFunctionGradientIntegral


set_option autoImplicit false

theorem _root_.solution (U : Set Plane) (hU : IsOpen U)
    (X : Plane → Plane) (hX : ContDiffOn ℝ 1 X U)
    (Y : Plane → Plane) (hY : ContDiff ℝ 1 Y) (hYsupp : HasCompactSupport Y)
    (hYU : tsupport Y ⊆ U) (e : Plane) :
    ∫ x in U, inner ℝ (fderiv ℝ X x e) (Y x)
      = - ∫ x in U, inner ℝ (X x) (fderiv ℝ Y x e) := by
  have hKc : IsCompact (tsupport Y) := hYsupp
  have hKcl : IsClosed (tsupport Y) := isClosed_tsupport Y
  have hXc : ContinuousOn X U := hX.continuousOn
  have hdXc : ContinuousOn (fderiv ℝ X) U := hX.continuousOn_fderiv_of_isOpen hU le_rfl
  have hYc : Continuous Y := hY.continuous
  have hdYc : Continuous (fderiv ℝ Y) := hY.continuous_fderiv one_ne_zero
  -- Vanishing off the support of `Y`.
  have hY0 : ∀ x, x ∉ tsupport Y → Y x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hdY0 : ∀ x, x ∉ tsupport Y → fderiv ℝ Y x = 0 := by
    intro x hx
    have hev : Y =ᶠ[nhds x] fun _ : Plane => (0 : Plane) :=
      notMem_tsupport_iff_eventuallyEq.mp hx
    rw [hev.fderiv_eq]
    simp
  -- The pairing, glued to a `C^1` function on the whole plane.
  obtain ⟨F, hFdef⟩ : ∃ f : Plane → ℝ, f = fun x => inner ℝ (X x) (Y x) := ⟨_, rfl⟩
  have hF0 : ∀ x, x ∉ tsupport Y → F x = 0 := by
    intro x hx
    rw [hFdef]
    show inner ℝ (X x) (Y x) = (0 : ℝ)
    rw [hY0 x hx, inner_zero_right]
  have hFev : ∀ x, x ∉ tsupport Y → F =ᶠ[nhds x] fun _ : Plane => (0 : ℝ) := by
    intro x hx
    filter_upwards [hKcl.isOpen_compl.mem_nhds hx] with y hy using hF0 y hy
  have hFC1 : ContDiff ℝ 1 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxU : x ∈ U
    · rw [hFdef]
      exact (hX.contDiffAt (hU.mem_nhds hxU)).inner ℝ hY.contDiffAt
    · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (hFev x (fun hc => hxU (hYU hc)))
  have hFsupp : HasCompactSupport F := HasCompactSupport.intro hKc hF0
  -- The integral of `D F` over the plane vanishes;  pair it with `e`.
  have hzero : ∫ x : Plane, gradient F x = 0 := TestFunctionGradientIntegral F hFC1 hFsupp
  have hgF0 : ∀ x, x ∉ tsupport Y → gradient F x = 0 := by
    intro x hx
    rw [(hFev x hx).gradient_eq, gradient_fun_const]
  have hgFc : Continuous (gradient F) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hFC1.continuous_fderiv one_ne_zero)
  have hgFint : MeasureTheory.Integrable (gradient F) :=
    hgFc.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc hgF0)
  have hpair : ∫ x : Plane, inner ℝ (gradient F x) e = (0 : ℝ) := by
    have hL := ContinuousLinearMap.integral_comp_comm (innerSL ℝ e) hgFint
    rw [hzero, map_zero] at hL
    have hc : ∀ x : Plane, (innerSL ℝ e) (gradient F x) = inner ℝ (gradient F x) e := by
      intro x
      show inner ℝ e (gradient F x) = inner ℝ (gradient F x) e
      exact real_inner_comm (gradient F x) e
    simp only [hc] at hL
    exact hL
  -- The product rule for the pairing.  It holds at EVERY point:  off `tsupport Y` all three
  -- terms vanish, and `tsupport Y ⊆ U`.
  have hgrad : ∀ x : Plane, inner ℝ (gradient F x) e
      = inner ℝ (fderiv ℝ X x e) (Y x) + inner ℝ (X x) (fderiv ℝ Y x e) := by
    intro x
    have hge : inner ℝ (gradient F x) e = fderiv ℝ F x e := by
      rw [← toDual_gradient]
      rfl
    rw [hge]
    by_cases hxU : x ∈ U
    · have hXd : HasFDerivAt X (fderiv ℝ X x) x :=
        (((hX.differentiableOn one_ne_zero) x hxU).differentiableAt
          (hU.mem_nhds hxU)).hasFDerivAt
      have hYd : HasFDerivAt Y (fderiv ℝ Y x) x := (hY.differentiable one_ne_zero x).hasFDerivAt
      have hFd : fderiv ℝ F x = (fderivInnerCLM ℝ (X x, Y x)).comp
          ((fderiv ℝ X x).prod (fderiv ℝ Y x)) := by
        rw [hFdef]
        exact (hXd.inner ℝ hYd).fderiv
      rw [hFd]
      show (fderivInnerCLM ℝ (X x, Y x)) (fderiv ℝ X x e, fderiv ℝ Y x e)
        = inner ℝ (fderiv ℝ X x e) (Y x) + inner ℝ (X x) (fderiv ℝ Y x e)
      rw [fderivInnerCLM_apply]
      exact add_comm _ _
    · have hxK : x ∉ tsupport Y := fun hc => hxU (hYU hc)
      rw [(hFev x hxK).fderiv_eq, hY0 x hxK, hdY0 x hxK]
      simp
  -- Both summands are continuous on the plane -- by the same gluing as for `F` -- and have
  -- compact support, hence are integrable.
  have hglue : ∀ f : Plane → ℝ, ContinuousOn f U → (∀ y, y ∉ tsupport Y → f y = 0) →
      MeasureTheory.Integrable f := by
    intro f hfc hf0
    have hfC : Continuous f := by
      rw [continuous_iff_continuousAt]
      intro x
      by_cases hxU : x ∈ U
      · exact (hfc x hxU).continuousAt (hU.mem_nhds hxU)
      · have hxK : x ∉ tsupport Y := fun hc => hxU (hYU hc)
        refine (continuousAt_const (y := (0 : ℝ))).congr ?_
        filter_upwards [hKcl.isOpen_compl.mem_nhds hxK] with y hy using (hf0 y hy).symm
    exact hfC.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc hf0)
  have hint1 : MeasureTheory.Integrable (fun x => inner ℝ (fderiv ℝ X x e) (Y x)) := by
    refine hglue _ ?_ ?_
    · exact ContinuousOn.inner (hdXc.clm_apply continuousOn_const) hYc.continuousOn
    · intro y hy
      rw [hY0 y hy, inner_zero_right]
  have hint2 : MeasureTheory.Integrable (fun x => inner ℝ (X x) (fderiv ℝ Y x e)) := by
    refine hglue _ ?_ ?_
    · exact ContinuousOn.inner hXc (hdYc.continuousOn.clm_apply continuousOn_const)
    · intro y hy
      rw [hdY0 y hy]
      simp
  -- Localization:  each summand vanishes off `U`, so its integral over `U` is over the plane.
  have hloc1 : ∫ x in U, inner ℝ (fderiv ℝ X x e) (Y x)
      = ∫ x : Plane, inner ℝ (fderiv ℝ X x e) (Y x) := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    rw [hY0 x (fun hc => hx (hYU hc)), inner_zero_right]
  have hloc2 : ∫ x in U, inner ℝ (X x) (fderiv ℝ Y x e)
      = ∫ x : Plane, inner ℝ (X x) (fderiv ℝ Y x e) := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    rw [hdY0 x (fun hc => hx (hYU hc))]
    simp
  -- Conclusion.
  have hrw : (fun x : Plane => inner ℝ (gradient F x) e)
      = fun x : Plane => inner ℝ (fderiv ℝ X x e) (Y x)
        + inner ℝ (X x) (fderiv ℝ Y x e) := funext hgrad
  rw [hrw, MeasureTheory.integral_add hint1 hint2] at hpair
  rw [hloc1, hloc2, eq_neg_iff_add_eq_zero]
  exact hpair
