-- Prove2me | solution 1 for CertDRO.NNSmooth.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:40:51.00015+00:00
-- url     : https://prove2.me/submissions/bd080793-6ec8-47f0-b9b6-6ccc48fb4ce1

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Network

set_option autoImplicit false

open CertDRO.NNSmooth CertDRO.NNSmooth.Network

theorem solution (N : Network) (L : ℕ) (hσ : ∀ l < L, Differentiable ℝ (N.σ l)) :
    (∀ l ≤ L, Differentiable ℝ (N.F l)) ∧
    (∀ l < L, ∀ x : E (N.dO 0),
      HasFDerivAt (N.F (l + 1))
        ((fderiv ℝ (N.σ l) (N.θ l (N.F l x))).comp ((N.θ l).comp (fderiv ℝ (N.F l) x))) x) ∧
    (∀ l ≤ L, ∀ x : E (N.dO 0), fderiv ℝ (N.F l) x = N.tailJac x 0 l) := by
  have hdiff : ∀ l ≤ L, Differentiable ℝ (N.F l) := by
    intro l
    induction l with
    | zero => intro _; exact differentiable_id
    | succ l ih =>
      intro hl
      have h1 := ih (by omega)
      have : N.F (l + 1) = fun x => N.σ l (N.θ l (N.F l x)) := rfl
      rw [this]
      exact (hσ l (by omega)).comp ((N.θ l).differentiable.comp h1)
  have hstep : ∀ l < L, ∀ x : E (N.dO 0),
      HasFDerivAt (N.F (l + 1))
        ((fderiv ℝ (N.σ l) (N.θ l (N.F l x))).comp ((N.θ l).comp (fderiv ℝ (N.F l) x))) x := by
    intro l hl x
    have h1 : HasFDerivAt (N.F l) (fderiv ℝ (N.F l) x) x :=
      ((hdiff l (by omega)) x).hasFDerivAt
    have h2 : HasFDerivAt (fun x => N.θ l (N.F l x)) ((N.θ l).comp (fderiv ℝ (N.F l) x)) x :=
      (N.θ l).hasFDerivAt.comp x h1
    have h3 : HasFDerivAt (N.σ l) (fderiv ℝ (N.σ l) (N.θ l (N.F l x))) (N.θ l (N.F l x)) :=
      ((hσ l hl) _).hasFDerivAt
    exact h3.comp x h2
  refine ⟨hdiff, hstep, ?_⟩
  intro l
  induction l with
  | zero =>
    intro _ x
    have : N.F 0 = id := rfl
    rw [this, fderiv_id]
    simp [Network.tailJac]
  | succ l ih =>
    intro hl x
    rw [(hstep l (by omega) x).fderiv, ih (by omega) x]
    rw [Network.tailJac, dif_neg (by omega)]
