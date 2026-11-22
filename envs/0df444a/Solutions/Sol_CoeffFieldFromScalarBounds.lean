-- Prove2me | solution 1 for CoeffFieldFromScalarBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:23:59.365426+00:00
-- url     : https://prove2.me/submissions/4e584a8c-d036-472d-8972-66cfc10b0aba

import Definitions.Def_PHigherOrder_CoeffFieldBounds
import Definitions.Def_PHigherOrder_GradientFieldOrderShift
import Definitions.Def_PHigherOrder_CoeffFieldFromScalarBounds
import Theorems.Thm_CoeffFieldBounds
import Theorems.Thm_GradientFieldOrderShift


set_option autoImplicit false

theorem _root_.solution (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    (j : ℕ) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (C D d : ℝ) (hC : 0 < C) (hD : 0 < D) (hd : 0 < d) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (U V : Set Plane) (Φ : Plane → W) (v : Plane → ℝ),
        IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
        IsOpen V → Convex ℝ V → (∀ x ∈ U, gradient v x ∈ V) →
        ContDiffOn ℝ (⊤ : ℕ∞) Φ V →
        (∀ i ≤ j + 1, ∀ ξ ∈ V, ‖iteratedFDeriv ℝ i Φ ξ‖ ≤ C) →
        ContDiffOn ℝ (⊤ : ℕ∞) v U →
        (∀ i ≤ j + 1, ∀ x ∈ U, ‖iteratedFDeriv ℝ i v x‖ ≤ D) →
        (∀ x ∈ U, ∀ y ∈ U,
            ‖iteratedFDeriv ℝ (j + 1) v x - iteratedFDeriv ℝ (j + 1) v y‖ ≤ D * ‖x - y‖ ^ κ) →
        (∀ i ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (Φ ∘ gradient v) x‖ ≤ M)
          ∧ (∀ x ∈ U, ∀ y ∈ U,
              ‖iteratedFDeriv ℝ j (Φ ∘ gradient v) x - iteratedFDeriv ℝ j (Φ ∘ gradient v) y‖
                ≤ M * ‖x - y‖ ^ κ) := by
  obtain ⟨M, hM, hCFB⟩ := CoeffFieldBounds W j κ hκ0 hκ1 C D d hC hD hd
  refine ⟨M, hM, ?_⟩
  intro U V Φ v hUo hUc hUd hVo hVc hHV hΦ hΦb hv hvb hvh
  -- The Riesz factorization of the gradient field, its smoothness, and the two sharp
  -- order-shift bridges, at a point and at a pair of points of `U`, all at no loss of
  -- constant: the conversion is an equality, not an estimate.
  obtain ⟨-, hgC, hbrSup, hbrHol⟩ := GradientFieldOrderShift U v hUo hv
  -- The composition estimate, with the converted hypotheses.
  refine hCFB U V Φ (gradient v) hUo hUc hUd hVo hVc hHV hΦ hΦb hgC ?_ ?_
  · intro i hi x hx
    rw [hbrSup i x]
    exact hvb (i + 1) (by omega) x hx
  · intro x hx y hy
    rw [hbrHol j x hx y hy]
    exact hvh x hx y hy
