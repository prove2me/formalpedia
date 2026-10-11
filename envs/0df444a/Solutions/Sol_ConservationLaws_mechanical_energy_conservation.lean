-- Prove2me | solution 1 for ConservationLaws.mechanical_energy_conservation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T21:06:59.263982+00:00
-- url     : https://prove2.me/submissions/bfe2c39f-59c2-4003-bb30-0504827842ff

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {d : ℕ} (m : ℝ) (hm : 0 < m)
    (V : EuclideanSpace ℝ (Fin d) → ℝ) (hV : Differentiable ℝ V)
    (x v a : ℝ → EuclideanSpace ℝ (Fin d))
    (hx : ∀ t, HasDerivAt x (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (hnewton : ∀ t, m • a t = -gradient V (x t)) :
    ∀ t s, (1 / 2 : ℝ) * m * ‖v t‖ ^ 2 + V (x t) =
      (1 / 2 : ℝ) * m * ‖v s‖ ^ 2 + V (x s) := by
  let E : ℝ → ℝ := fun t => (1 / 2 : ℝ) * m * ‖v t‖ ^ 2 + V (x t)
  have hkin (t : ℝ) :
      HasDerivAt (fun q => (1 / 2 : ℝ) * m * ‖v q‖ ^ 2)
        (inner ℝ (m • a t) (v t)) t := by
    have hsq := ((hv t).norm_sq).const_mul ((1 / 2 : ℝ) * m)
    have heq : ((1 / 2 : ℝ) * m) *
        (2 * inner ℝ (v t) (a t)) = inner ℝ (m • a t) (v t) := by
      calc
        _ = m * inner ℝ (v t) (a t) := by ring
        _ = inner ℝ (m • a t) (v t) := by
          simp [real_inner_comm, inner_smul_left]
    rw [heq] at hsq
    exact hsq
  have hpotential (t : ℝ) :
      HasDerivAt (fun q => V (x q))
        (inner ℝ (gradient V (x t)) (v t)) t := by
    have hVderiv : HasFDerivAt V (fderiv ℝ V (x t)) (x t) :=
      (hV (x t)).hasFDerivAt
    have hxderiv : HasDerivAt x (v t) t := hx t
    have hc : HasDerivAt (V ∘ x) ((fderiv ℝ V (x t)) (v t)) t :=
      HasFDerivAt.comp_hasDerivAt (l := V) (f := x) (x := t)
        hVderiv hxderiv
    simpa only [Function.comp_def, inner_gradient_left] using hc
  have hzero (t : ℝ) :
      inner ℝ (m • a t) (v t) +
        inner ℝ (gradient V (x t)) (v t) = 0 := by
    rw [hnewton t]
    simp
  have hE (t : ℝ) : HasDerivAt E 0 t := by
    have hh := (hkin t).add (hpotential t)
    change HasDerivAt E
      (inner ℝ (m • a t) (v t) +
        inner ℝ (gradient V (x t)) (v t)) t at hh
    rw [hzero t] at hh
    exact hh
  have hdiff : Differentiable ℝ E :=
    fun t => (hE t).differentiableAt
  have hderiv : ∀ t, deriv E t = 0 := fun t => (hE t).deriv
  intro t s
  exact is_const_of_deriv_eq_zero hdiff hderiv t s
