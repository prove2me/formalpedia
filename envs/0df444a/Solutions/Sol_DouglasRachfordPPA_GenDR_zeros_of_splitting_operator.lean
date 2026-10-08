-- Prove2me | solution 1 for DouglasRachfordPPA.GenDR.zeros_of_splitting_operator
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:21:57.158809+00:00
-- url     : https://prove2.me/submissions/47104bed-4d39-423e-9e49-18e1c4043a1c

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_DouglasRachfordPPA_GenDR_SplittingOperator

open InnerProductSpace ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (lam : ℝ) (hlam : 0 < lam) (A B : H → Set H) :
    zer (splittingOp lam A B) = Zstar lam A B ∧
    Zstar lam A B ⊆ {z | ∃ u b : H, u ∈ zer (opAdd A B) ∧ b ∈ B u ∧ z = u + lam • b} := by
  refine ⟨?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨u, b, v, a, hb, ha, heq, hz, h0⟩
      have huv : u = v := (sub_eq_zero.mp h0.symm)
      subst huv
      have hab : lam • a = -(lam • b) := by
        have := heq
        rw [sub_eq_add_neg] at this
        exact add_left_cancel this
      have ha' : a = -b := by
        rw [← smul_neg] at hab
        exact smul_right_injective H hlam.ne' hab
      subst ha'
      exact ⟨u, b, hb, ha, hz⟩
    · rintro ⟨u, b, hb, ha, hz⟩
      refine ⟨u, b, u, -b, hb, ha, ?_, hz, (sub_self u).symm⟩
      rw [smul_neg, sub_eq_add_neg]
  · rintro z ⟨u, b, hb, ha, hz⟩
    exact ⟨u, b, ⟨-b, ha, b, hb, (neg_add_cancel b).symm⟩, hb, hz⟩
