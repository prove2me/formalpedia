-- Prove2me | solution 1 for Everyday.everyday_phase
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:23:11.423501+00:00
-- url     : https://prove2.me/submissions/cc95717e-3e20-4c75-8b26-a1cd82dbc290

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

open Everyday
/-- The everyday equation's amplitude is a phase: assemble the four
labeled sectors — gravity, the other forces, matter (the Yukawa term
plus its hermitian conjugate), and the Higgs potential — into the action
of a configuration; the action is real, so the exponential of i times it
has modulus exactly one. This is the quantum-mechanical heart of the
source equation: the everyday world's dynamics is one real functional
whose exponentiation gives the transition amplitude. -/


theorem solution {X : Type} [Fintype X] (vol : X → ℝ) (w : X → X → X → ℝ)
    (mp : ℝ) (R : X → ℝ) (A : X → X → ℝ) (ψL ψR : X → ℂ) (V : ℂ) (Φh : X → ℂ)
    (μ lam : ℝ) :
    ‖Complex.exp
      (Complex.I * everydayAction vol w mp R A ψL ψR V Φh μ lam)‖ = 1 := by
  have h : everydayAction vol w mp R A ψL ψR V Φh μ lam
      = ((everydayAction vol w mp R A ψL ψR V Φh μ lam).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp only [everydayAction, Complex.add_im, Complex.ofReal_im, Complex.conj_im]
      ring
  rw [h, mul_comm]; exact Complex.norm_exp_ofReal_mul_I _


