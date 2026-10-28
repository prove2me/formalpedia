-- Prove2me | solution 1 for ContinuityEqWiki.optical_flow_equation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:15:11.887856+00:00
-- url     : https://prove2.me/submissions/b8433153-5ef2-4eb5-b4ca-87bf9977d80b

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

open ContinuityEqWiki

theorem solution (I : ℝ → (Fin 2 → ℝ) → ℝ) (V : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ)
    (p : ℝ → Fin 2 → ℝ) (hI : ContDiff ℝ 1 (Function.uncurry I))
    (hp : ∀ t, HasDerivAt p (V t (p t)) t)
    (brightness_constancy : ∀ s t, I s (p s) = I t (p t)) :
    ∀ t, partialDeriv 0 (I t) (p t) * V t (p t) 0 + partialDeriv 1 (I t) (p t) * V t (p t) 1
      + timeDeriv I t (p t) = 0 := by
  intro t
  set Φ := Function.uncurry I with hΦdef
  set DΦ := fderiv ℝ Φ (t, p t)
  have hΦ : HasFDerivAt Φ DΦ (t, p t) := ((hI.differentiable one_ne_zero) _).hasFDerivAt
  set v := V t (p t)
  -- total derivative along the path is zero
  have h1 : HasDerivAt (Φ ∘ fun s => (s, p s)) (DΦ ((1 : ℝ), v)) t :=
    hΦ.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hp t))
  have hconst : (Φ ∘ fun s => (s, p s)) = fun _ => I t (p t) := by
    funext s; exact brightness_constancy s t
  rw [hconst] at h1
  have hzero : DΦ ((1 : ℝ), v) = 0 := h1.unique (hasDerivAt_const t _)
  -- time derivative
  have h2 : HasDerivAt (Φ ∘ fun s => (s, p t)) (DΦ ((1 : ℝ), (0 : Fin 2 → ℝ))) t :=
    hΦ.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t (p t)))
  have htime : timeDeriv I t (p t) = DΦ ((1 : ℝ), (0 : Fin 2 → ℝ)) := h2.deriv
  -- spatial derivatives
  have hsp : ∀ k : Fin 2, partialDeriv k (I t) (p t) = DΦ ((0 : ℝ), Pi.single k 1) := by
    intro k
    have h3 : HasFDerivAt (fun y : Fin 2 → ℝ => ((t, y) : ℝ × (Fin 2 → ℝ)))
        ((0 : (Fin 2 → ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Fin 2 → ℝ))) (p t) :=
      (hasFDerivAt_const t (p t)).prodMk (hasFDerivAt_id (p t))
    have h4 := hΦ.comp (p t) h3
    unfold partialDeriv
    have : I t = Φ ∘ (fun y : Fin 2 → ℝ => ((t, y) : ℝ × (Fin 2 → ℝ))) := rfl
    rw [this, h4.fderiv]
    simp
  have hdecomp : ((1 : ℝ), v) = ((1 : ℝ), (0 : Fin 2 → ℝ)) + v 0 • ((0 : ℝ), Pi.single 0 1)
      + v 1 • ((0 : ℝ), Pi.single 1 1) := by
    ext k
    · simp
    · fin_cases k <;> simp
  rw [hdecomp, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hzero
  rw [hsp 0, hsp 1, htime]
  linarith
