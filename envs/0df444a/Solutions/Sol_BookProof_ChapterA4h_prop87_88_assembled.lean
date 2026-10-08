-- Prove2me | solution 1 for BookProof.ChapterA4h.prop87_88_assembled
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:55:38.164987+00:00
-- url     : https://prove2.me/submissions/1aba7bf7-c08e-4cef-b559-59713779380b

import Mathlib
import Definitions.Def_ChapterA4h
open Matrix BookProof.ChapterA3 BookProof.ChapterA4e BookProof.ChapterA4f BookProof.ChapterA5 BookProof.ChapterA4h
set_option maxHeartbeats 0
variable (R : Type*)

theorem solution (Mk : MackeyImprimitivity R)
    (Wg : WignerClassification R Mk) (ρ : R) :
    (PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.massive ∨
      PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.masslessDiscrete) ∧
    ¬ ∀ j : Fin 3, projPos * spatialOp j = spatialOp j * projPos := by
  constructor
  ·
    have hnn : 0 ≤ Mk.massSq ρ := by
      unfold MackeyImprimitivity.massSq
      positivity
    unfold PoincareType.of
    rcases lt_or_eq_of_le hnn with h | h
    · left; simp [h]
    · right
      rw [← h]
      simp [Wg.no_continuous_spin ρ h.symm]
  ·
    intro h
    have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => (M 0 0).im) (h 0)
    norm_num [projPos, enSign, spatialOp, coeffMass1Z, coeffBoostZ,
      spatialIdx, mgammaZ, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ, Fin.ofNat, Fin.succ,
      Matrix.smul_apply, Matrix.map_apply, RingHom.mapMatrix_apply,
      Complex.mul_re, Complex.mul_im, Complex.inv_re,
      Complex.inv_im, Complex.normSq] at he

#print axioms solution

