-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.star_dot_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T08:52:48.624471+00:00
-- url     : https://prove2.me/submissions/27d64a37-1f31-4e41-b023-5f10aad572a5

import Mathlib

noncomputable section
open Matrix Complex

variable {m : Type} [Fintype m] [DecidableEq m]

theorem solution (w : m → ℂ) : star w ⬝ᵥ w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    ← Complex.ofReal_sum]
