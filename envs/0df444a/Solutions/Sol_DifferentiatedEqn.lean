-- Prove2me | solution 1 for DifferentiatedEqn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:18:12.363095+00:00
-- url     : https://prove2.me/submissions/a9e67a2d-785e-49f9-94fc-6e03aba36eb2

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_FluxJacobianElliptic
import Definitions.Def_PHigherOrder_IsLinearDivSol
import Definitions.Def_PHigherOrder_ClassicalGradIsWeakGrad
import Definitions.Def_PHigherOrder_DirectionalIntegrationByParts
import Definitions.Def_PHigherOrder_DifferentiatedEqn
import Theorems.Thm_ClassicalGradIsWeakGrad
import Theorems.Thm_DirectionalIntegrationByParts
import Theorems.Thm_FluxJacobianElliptic


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (U : Set Plane)
    (v : Plane → ℝ)
    (hv : IsPHarm p U v (gradient v)) (hsm : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (hne : ∀ x ∈ U, gradient v x ≠ 0) (e : Plane) :
    IsLinearDivSol U (fun x => FluxJacobian p (gradient v x))
      (fun x => inner ℝ (gradient v x) e)
      (fun x => gradient (fun y => inner ℝ (gradient v y) e) x) := by
  have hU : IsOpen U := hv.openOmega
  -- STEP 1 (regularity).  The gradient field is the Riesz transport of the Frechet derivative,
  -- so its regularity is that of the derivative.
  have hgradeq : ∀ f : Plane → ℝ,
      gradient f
        = (fun A : Plane →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ Plane).symm A) ∘ fderiv ℝ f := by
    intro f
    funext x
    show gradient f x = (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ f x)
    rw [← toDual_gradient, LinearIsometryEquiv.symm_apply_apply]
  have hgreg : ∀ f : Plane → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f U →
      ContDiffOn ℝ (⊤ : ℕ∞) (gradient f) U := by
    intro f hf
    rw [hgradeq f]
    exact (InnerProductSpace.toDual ℝ Plane).symm.contDiff.comp_contDiffOn
      (hf.fderiv_of_isOpen hU (by norm_cast))
  have hgregC : ∀ f : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) (gradient f) := by
    intro f hf
    rw [hgradeq f]
    exact (InnerProductSpace.toDual ℝ Plane).symm.contDiff.comp
      (hf.fderiv_right (by norm_cast))
  -- The second derivative is symmetric, in gradient form:  `d_e (Df) = D (d_e f)`.  This is
  -- clause (3) of the background proposition on the gradient field and directional derivatives,
  -- and it is used twice below -- for `v` on `U` in Step 2, and for the test function on the
  -- whole plane in Step 5.
  have hsymm : ∀ (V : Set Plane), IsOpen V → ∀ f : Plane → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f V →
      ∀ x ∈ V, ∀ d : Plane,
        fderiv ℝ (gradient f) x d = gradient (fun y => inner ℝ (gradient f y) d) x := by
    intro V hV f hf x hx d
    have hfd1 : ∀ᶠ y in nhds x, HasFDerivAt f (fderiv ℝ f y) y := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact ((hf.differentiableOn (by norm_cast) y hy).differentiableAt
        (hV.mem_nhds hy)).hasFDerivAt
    have hfd2 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x := by
      have h := (hf.fderiv_of_isOpen hV (m := (1 : ℕ)) (by norm_cast)).differentiableOn
        (by norm_cast) x hx
      exact (h.differentiableAt (hV.mem_nhds hx)).hasFDerivAt
    have hsym := second_derivative_symmetric_of_eventually hfd1 hfd2
    have hd1 : HasFDerivAt (gradient f)
        (((InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearMap).comp
          (fderiv ℝ (fderiv ℝ f) x)) x := by
      rw [hgradeq f]
      exact ((InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearMap.hasFDerivAt).comp x hfd2
    have hgeq : (fun y => inner ℝ (gradient f y) d) = fun y => (fderiv ℝ f y) d := by
      funext y
      rw [← toDual_gradient]
      rfl
    have hd2 : HasFDerivAt (fun y => inner ℝ (gradient f y) d)
        ((ContinuousLinearMap.apply ℝ ℝ d).comp (fderiv ℝ (fderiv ℝ f) x)) x := by
      rw [hgeq]
      exact ((ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt).comp x hfd2
    refine ext_inner_right ℝ ?_
    intro z
    have hA : inner ℝ (fderiv ℝ (gradient f) x d) z = fderiv ℝ (fderiv ℝ f) x d z := by
      rw [hd1.fderiv]
      show inner ℝ ((InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ (fderiv ℝ f) x d)) z = _
      exact InnerProductSpace.toDual_symm_apply
    have hB : inner ℝ (gradient (fun y => inner ℝ (gradient f y) d) x) z
        = fderiv ℝ (fderiv ℝ f) x z d := by
      have h1 : (InnerProductSpace.toDual ℝ Plane)
          (gradient (fun y => inner ℝ (gradient f y) d) x) z
          = fderiv ℝ (fun y => inner ℝ (gradient f y) d) x z := by
        rw [toDual_gradient]
      rw [hd2.fderiv] at h1
      exact h1
    rw [hA, hB]
    exact hsym d z
  have hxi : ContDiffOn ℝ (⊤ : ℕ∞) (gradient v) U := hgreg v hsm
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => inner ℝ (gradient v x) e) U :=
    hxi.inner ℝ contDiffOn_const
  have hG : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => gradient (fun y => inner ℝ (gradient v y) e) x) U := hgreg _ hw
  refine ⟨hw.continuousOn, ?_, ?_, ?_, ?_⟩
  · -- STEP 3, condition (2):  measurability of `G`.
    exact hG.continuousOn.aestronglyMeasurable hU.measurableSet
  · -- STEP 3, condition (3):  local square integrability of `G`.
    intro K hKU hK
    exact ContinuousOn.integrableOn_compact hK (((hG.continuousOn.norm).pow 2).mono hKU)
  · -- STEP 4, condition (4):  `G` is the distributional gradient of `w`.
    exact ClassicalGradIsWeakGrad U hU (fun x => inner ℝ (gradient v x) e)
      (hw.of_le (by exact_mod_cast le_top))
  · -- STEP 5, condition (5):  the weak equation.
    intro φ hφ hφsupp hφU
    have hfje := FluxJacobianElliptic p hp hp2 1 1 one_pos le_rfl
    -- `X = A_p ∘ Dv` is of class `C^1` on `U`  (Step 1).
    have hmaps : Set.MapsTo (gradient v) U {ζ : Plane | ζ ≠ 0} := fun x hx => hne x hx
    have hXC1 : ContDiffOn ℝ 1 (fun x => PFlux p (gradient v x)) U :=
      (hfje.2.2.2.2.2.2.comp hxi hmaps).of_le (by exact_mod_cast le_top)
    -- STEP 2:  the chain rule in the direction `e`, `d_e X = A (G)` on `U`.
    have hXfd : ∀ x ∈ U, fderiv ℝ (fun y => PFlux p (gradient v y)) x e
        = FluxJacobian p (gradient v x)
            (gradient (fun y => inner ℝ (gradient v y) e) x) := by
      intro x hx
      have hxid : HasFDerivAt (gradient v) (fderiv ℝ (gradient v) x) x :=
        ((hxi.differentiableOn (by norm_cast) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
      have hAd : HasFDerivAt (PFlux p) (FluxJacobian p (gradient v x)) (gradient v x) :=
        hfje.1 _ (hne x hx)
      have hc : HasFDerivAt (fun y => PFlux p (gradient v y))
          ((FluxJacobian p (gradient v x)).comp (fderiv ℝ (gradient v) x)) x := hAd.comp x hxid
      rw [hc.fderiv]
      show FluxJacobian p (gradient v x) (fderiv ℝ (gradient v) x e) = _
      rw [hsymm U hU v hsm x hx e]
    -- (5b) `Dφ` is of class `C^1` on the plane, with compact support inside `U`.
    have hgφ : ContDiff ℝ (⊤ : ℕ∞) (gradient φ) := hgregC φ hφ
    have hgφsupp : HasCompactSupport (gradient φ) := by
      rw [hgradeq φ]
      exact (hφsupp.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ Plane).symm)
    have hgφU : tsupport (gradient φ) ⊆ U := by
      rw [hgradeq φ]
      exact ((tsupport_comp_subset (map_zero (InnerProductSpace.toDual ℝ Plane).symm)
        (fderiv ℝ φ)).trans (tsupport_fderiv_subset ℝ)).trans hφU
    -- (5a) `d_e φ` is again a test function, so the weak equation applies to it.
    have hψeq : (fun x => inner ℝ (gradient φ x) e)
        = (fun z : Plane => inner ℝ z e) ∘ gradient φ := rfl
    have hweak := hv.eqn (fun x => inner ℝ (gradient φ x) e) (hgφ.inner ℝ contDiff_const)
      (by rw [hψeq]; exact hgφsupp.comp_left (inner_zero_left e))
      (by rw [hψeq]; exact (tsupport_comp_subset (inner_zero_left e) (gradient φ)).trans hgφU)
    -- (5c) integration by parts in the direction `e`.
    have hibp := DirectionalIntegrationByParts U hU (fun x => PFlux p (gradient v x)) hXC1
      (gradient φ) (hgφ.of_le (by exact_mod_cast le_top)) hgφsupp hgφU e
    have hRHS : ∫ x in U, inner ℝ (PFlux p (gradient v x)) (fderiv ℝ (gradient φ) x e)
        = (0 : ℝ) := by
      rw [← hweak]
      refine MeasureTheory.setIntegral_congr_fun hU.measurableSet ?_
      intro x _
      dsimp only
      rw [hsymm Set.univ isOpen_univ φ hφ.contDiffOn x (Set.mem_univ x) e]
    -- (5d) conclusion.
    have hgoal : ∫ x in U, inner ℝ (FluxJacobian p (gradient v x)
          (gradient (fun y => inner ℝ (gradient v y) e) x)) (gradient φ x)
        = ∫ x in U, inner ℝ (fderiv ℝ (fun y => PFlux p (gradient v y)) x e)
            (gradient φ x) := by
      refine MeasureTheory.setIntegral_congr_fun hU.measurableSet ?_
      intro x hx
      dsimp only
      rw [hXfd x hx]
    rw [hgoal, hibp, hRHS, neg_zero]
