-- Prove2me | solution 1 for DynMomentum.ShortHorizon.eq_A9_solves_A8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:39:30.547662+00:00
-- url     : https://prove2.me/submissions/e0411cab-81f7-4de1-8a3f-8a5369976db4

import Mathlib
import Definitions.Def_DynMomentum_ShortHorizon_Model

open DynMomentum.ShortHorizon


theorem solution (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (s : ℝ → ℝ) (hs : ContinuousOn s (Set.Icc (-P.τ) 0)) (A1 A2 A3 : ℝ → ℝ)
    (hA : SolvesA9Full P T s A1 A2 A3) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ,
      HasDerivWithinAt (fun t' => ansatz A1 A2 A3 x t')
        (-(pdeDrift P s t x * deriv (fun y => ansatz A1 A2 A3 y t) x
            + P.σ ^ 2 / 2 * deriv (deriv (fun y => ansatz A1 A2 A3 y t)) x
            + pdePotential P s t x * ansatz A1 A2 A3 x t))
        (Set.Icc 0 T) t) ∧
    ∀ x : ℝ, ansatz A1 A2 A3 x T = 1 := by
  obtain ⟨⟨h1, h2, hT1, hT2⟩, h3, hT3⟩ := hA
  refine ⟨fun t ht x => ?_, fun x => ?_⟩
  · have hx1 : ∀ y, HasDerivAt (fun y => ansatz A1 A2 A3 y t)
        (ansatz A1 A2 A3 y t * (A1 t * y + A2 t)) y := by
      intro y
      have hg : HasDerivAt (fun y => A1 t * y ^ 2 / 2 + A2 t * y + A3 t) (A1 t * y + A2 t) y := by
        have := ((((hasDerivAt_pow 2 y).const_mul (A1 t)).div_const 2).add
          ((hasDerivAt_id y).const_mul (A2 t))).add_const (A3 t)
        refine this.congr_deriv ?_
        simp; ring
      exact hg.exp
    have hd1 : deriv (fun y => ansatz A1 A2 A3 y t) =
        fun y => ansatz A1 A2 A3 y t * (A1 t * y + A2 t) := funext fun y => (hx1 y).deriv
    have hd2 : deriv (deriv (fun y => ansatz A1 A2 A3 y t)) x =
        ansatz A1 A2 A3 x t * ((A1 t * x + A2 t) ^ 2 + A1 t) := by
      rw [hd1]
      have hl : HasDerivAt (fun y => A1 t * y + A2 t) (A1 t) x := by
        have := ((hasDerivAt_id x).const_mul (A1 t)).add_const (A2 t)
        simpa using this
      rw [((hx1 x).fun_mul hl).deriv]
      ring
    rw [hd2, hd1]
    have hg : HasDerivWithinAt (fun t' => A1 t' * x ^ 2 / 2 + A2 t' * x + A3 t')
        (rhs1 P (A1 t) * x ^ 2 / 2 + rhs2 P s t (A1 t) (A2 t) * x + rhs3 P s t (A1 t) (A2 t))
        (Set.Icc 0 T) t :=
      (((h1 t ht).mul_const (x ^ 2)).div_const 2).add ((h2 t ht).mul_const x) |>.add (h3 t ht)
    have he := hg.exp
    refine he.congr_deriv ?_
    unfold ansatz rhs1 rhs2 rhs3 pdeDrift pdePotential
    ring
  · unfold ansatz
    rw [hT1, hT2, hT3]
    simp
