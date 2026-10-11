-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.hermMat_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:30.763998+00:00
-- url     : https://prove2.me/submissions/7e1b82b8-b454-488f-90c0-8067143a31ad

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.hermMat_injective
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution {x y : Fin 4 → ℝ} (h : hermMat x = hermMat y) :
    x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 ∧ x 3 = y 3 := by

  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  have h01 := congrFun (congrFun h 0) 1
  simp only [hermMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h11 h01
  rw [Complex.ext_iff] at h00 h11 h01
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    at h00 h11 h01
  exact ⟨by linarith [h00.1, h11.1], by linarith [h01.1], by linarith [h01.2],
    by linarith [h00.1, h11.1]⟩
