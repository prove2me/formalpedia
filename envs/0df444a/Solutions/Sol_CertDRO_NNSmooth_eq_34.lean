-- Prove2me | solution 1 for CertDRO.NNSmooth.eq_34
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:43:23.194911+00:00
-- url     : https://prove2.me/submissions/1efe5f20-3e28-407d-8f08-c726b01b1747

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Network

set_option autoImplicit false

open CertDRO.NNSmooth CertDRO.NNSmooth.Network

theorem solution (N : Network) (L : ℕ) (hσ : ∀ l < L, Differentiable ℝ (N.σ l)) :
    ∀ l ≤ L, ∀ x x' : E (N.dO 0),
      fderiv ℝ (N.F l) x - fderiv ℝ (N.F l) x' =
        ∑ j ∈ Finset.range l, (N.tailJac x' (j + 1) l).comp
          ((fderiv ℝ (N.σ j) (N.θ j (N.F j x)) - fderiv ℝ (N.σ j) (N.θ j (N.F j x'))).comp
            ((N.θ j).comp (fderiv ℝ (N.F j) x))) := by
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
      fderiv ℝ (N.F (l + 1)) x =
        (fderiv ℝ (N.σ l) (N.θ l (N.F l x))).comp ((N.θ l).comp (fderiv ℝ (N.F l) x)) := by
    intro l hl x
    have h1 : HasFDerivAt (N.F l) (fderiv ℝ (N.F l) x) x :=
      ((hdiff l (by omega)) x).hasFDerivAt
    have h2 : HasFDerivAt (fun x => N.θ l (N.F l x)) ((N.θ l).comp (fderiv ℝ (N.F l) x)) x :=
      (N.θ l).hasFDerivAt.comp x h1
    have h3 : HasFDerivAt (N.σ l) (fderiv ℝ (N.σ l) (N.θ l (N.F l x))) (N.θ l (N.F l x)) :=
      ((hσ l hl) _).hasFDerivAt
    exact (h3.comp x h2).fderiv
  intro l
  induction l with
  | zero =>
    intro _ x x'
    have : N.F 0 = id := rfl
    simp [this]
  | succ l ih =>
    intro hl x x'
    have ih' := ih (by omega) x x'
    rw [hstep l (by omega) x, hstep l (by omega) x', Finset.sum_range_succ]
    have hid : N.tailJac x' (l + 1) (l + 1) = ContinuousLinearMap.id ℝ _ := by
      simp [Network.tailJac]
    have hjeq : ∀ j ∈ Finset.range l, N.tailJac x' (j + 1) (l + 1) =
        (fderiv ℝ (N.σ l) (N.θ l (N.F l x'))).comp ((N.θ l).comp (N.tailJac x' (j + 1) l)) := by
      intro j hj
      have hjl : j < l := Finset.mem_range.mp hj
      rw [Network.tailJac, dif_neg (by omega)]
    rw [Finset.sum_congr rfl (fun j hj' => by rw [hjeq j hj']), hid]
    set A := fderiv ℝ (N.σ l) (N.θ l (N.F l x))
    set A' := fderiv ℝ (N.σ l) (N.θ l (N.F l x'))
    set T := N.θ l
    set J := fderiv ℝ (N.F l) x
    set J' := fderiv ℝ (N.F l) x'
    have hsum : ∑ j ∈ Finset.range l,
        (A'.comp (T.comp (N.tailJac x' (j + 1) l))).comp
          ((fderiv ℝ (N.σ j) (N.θ j (N.F j x)) - fderiv ℝ (N.σ j) (N.θ j (N.F j x'))).comp
            ((N.θ j).comp (fderiv ℝ (N.F j) x))) = A'.comp (T.comp (J - J')) := by
      rw [ih']
      ext w
      simp [map_sum]
    rw [hsum]
    ext w
    simp
