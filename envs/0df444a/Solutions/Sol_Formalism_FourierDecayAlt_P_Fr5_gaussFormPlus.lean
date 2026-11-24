-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.gaussFormPlus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:11.114522+00:00
-- url     : https://prove2.me/submissions/5e348fd4-161d-4112-ae0e-bd3062450069

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_io_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_io_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_freeOf2_of_four_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_gauss_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_lam_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_mem_GG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_star_GG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_io_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_l
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_star_d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_comm_d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_insert_diagonal_extract
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_freeOf_diagScalar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr5
theorem _root_.solution (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ) (H : PlusHyp L f a Ya) :
    f.RR * ins a (f.TT Ya) = star (ins a !![1, 0; f.l L Ya, 1] * f.F) *
      (f.d L * ins a !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya]) *
      (ins a !![1, 0; f.l L Ya, 1] * f.F) := by
  obtain ⟨hs, h, hfree, hreal, hYa, hYa1, hq⟩ := H
  obtain ⟨fRR, fTT, fF, fFi, fx, fxi, fc, fci, fee⟩ := hfree
  have hfree : f.Free a := ⟨fRR, fTT, fF, fFi, fx, fxi, fc, fci, fee⟩
  have rYa := h.inv_reg hYa
  have rYa1 := h.inv_reg hYa1

  have hGx : ∀ Y, Commute (io L.GG) (f.x Y) := fun Y => (h.x_fn Y _ (mem_GG L)).symm
  have hτs : star (io L.GG * f.x Ya) = io L.GG * f.x Ya := by
    rw [star_mul, io_star, star_GG hs, h.x_star Ya hreal]; exact (hGx Ya).eq.symm
  have hτd : Commute (io L.GG * f.x Ya) (f.d L) :=
    (comm_d L f (io_fn_comm L (mem_GG L)) (h.c_fn _ (mem_GG L)).symm).mul_left
      (comm_d L f (h.x_fn Ya) (h.x_c Ya))
  have hdτ : star (f.d L * (io L.GG * f.x Ya)) = f.d L * (io L.GG * f.x Ya) := by
    rw [star_mul, hτs, star_d hs h]; exact hτd.eq
  have hGG1 : (io L.GG : SlopeTestRemainingChoices S A) * io L.GGi = 1 := by rw [← io_mul, L.GG_GGi, io_one]
  have hGG2 : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by rw [← io_mul, L.GGi_GG, io_one]
  have hinv1 : ∀ Y ∈ f.inv, (io L.GGi * f.xi Y) * (io L.GG * f.x Y) = 1 := by
    intro Y hY
    calc (io L.GGi * f.xi Y) * (io L.GG * f.x Y) = io L.GGi * f.xi Y * (f.x Y * io L.GG) := by rw [(hGx Y).eq]
      _ = io L.GGi * (f.xi Y * f.x Y) * io L.GG := by simp only [mul_assoc]
      _ = 1 := by rw [(h.x_xi Y hY).2, mul_one, hGG2]
  have hinv2 : ∀ Y ∈ f.inv, (io L.GG * f.x Y) * (io L.GGi * f.xi Y) = 1 := by
    intro Y hY
    calc (io L.GG * f.x Y) * (io L.GGi * f.xi Y) = f.x Y * (io L.GG * io L.GGi) * f.xi Y := by
          rw [(hGx Y).eq]; simp only [mul_assoc]
      _ = 1 := by rw [hGG1, mul_one, (h.x_xi Y hY).1]

  have herm : star (f.RR * f.TT Ya 1 0) = f.RR * f.TT Ya 0 1 := by
    have e := congrFun (congrFun (h.module.herm Ya rYa hreal) 0) 1
    unfold d0 at e
    rwa [Matrix.conjTranspose_apply, Matrix.diagonal_mul, Matrix.diagonal_mul] at e
  have hdet := (h.module.det Ya rYa rYa1).2
  have quantum_determinant_shifted : f.TT Ya 0 0 * f.TT (Ya + 1) 1 1 - f.TT Ya 0 1 * f.TT (Ya + 1) 1 0 = f.q Ya • (1 : SlopeTestRemainingChoices S A) := by
    have e := congrFun (congrFun hdet 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J, Matrix.transpose_apply, Matrix.smul_apply] at e
    simp at e
    rw [Algebra.smul_def, mul_one, ← e]; abel
  have upper_block_det_one : f.TT Ya 1 0 * f.TT (Ya + 1) 1 1 = f.TT Ya 1 1 * f.TT (Ya + 1) 1 0 := by
    have e := congrFun (congrFun hdet 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J, Matrix.transpose_apply, Matrix.smul_apply] at e
    simp at e
    rw [← sub_eq_zero, ← e]; abel
  obtain ⟨e11, e10, e01, e00⟩ := core f.F f.Fi (f.d L) (io L.GG * f.x Ya) (io L.GGi * f.xi Ya)
    (io L.GG * f.x (Ya + 1)) (io L.GGi * f.xi (Ya + 1)) (f.l L Ya) f.RR (f.TT Ya 0 0) (f.TT Ya 0 1) (f.TT Ya 1 0)
    (f.TT Ya 1 1) (f.TT (Ya + 1) 1 0) (f.TT (Ya + 1) 1 1) (f.q Ya) h.form h.F_Fi h.Fi_F hdτ (hinv1 Ya hYa)
    (hinv2 _ hYa1) (hinv1 _ hYa1) (h.frame_τ Ya rYa) (h.frame_l Ya hYa hYa1) (h.frame_τ _ rYa1) herm quantum_determinant_shifted upper_block_det_one

  have fl := free_l L f hfree Ya
  have fd := free_d L f hfree
  have fΛ : FreeOf2 a !![1, 0; f.l L Ya, 1] := freeOf2_of_four_entries (free_one a) (free_zero a) fl (free_one a)
  have fΛs : FreeOf2 a !![1, star (f.l L Ya); 0, 1] :=
    freeOf2_of_four_entries (free_one a) (free_star fl) (free_zero a) (free_one a)
  have fD : FreeOf2 a !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya] :=
    freeOf2_of_four_entries (free_smul _ (free_mul (free_io a _) (fxi _))) (free_zero a) (free_zero a)
      (free_mul (free_io a _) (fx _))
  have f1 := Wd4.freeOf_diagScalar (free_star fF)
  have f2 := Wd4.freeOf2_mul f1 fΛs
  have f3 := Wd4.freeOf2_mul f2 (Wd4.freeOf_diagScalar fd)
  have f4 := Wd4.freeOf2_mul f3 fD
  have f5 := Wd4.freeOf2_mul f4 fΛ
  have R : star (ins a !![1, 0; f.l L Ya, 1] * f.F) *
      (f.d L * ins a !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya]) *
      (ins a !![1, 0; f.l L Ya, 1] * f.F) =
      ins a (d0 (star f.F) * !![1, star (f.l L Ya); 0, 1] * d0 (f.d L) *
        !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya] * !![1, 0; f.l L Ya, 1] * d0 f.F) := by
    rw [Wd1.ins_mul a _ _ f5, Wd1.ins_mul a _ _ f4, Wd1.ins_mul a _ _ f3, Wd1.ins_mul a _ _ f2,
      Wd1.ins_mul a _ _ f1, Wd1.insert_diagonal_extract, Wd1.insert_diagonal_extract, Wd1.insert_diagonal_extract, star_mul, Wd1.ins_star a _ fΛ, lam_conj]
    simp only [mul_assoc]
  have Lh : f.RR * ins a (f.TT Ya) = ins a (d0 f.RR * f.TT Ya) := by
    rw [Wd1.ins_mul a _ _ (Wd4.freeOf_diagScalar fRR), Wd1.insert_diagonal_extract]
  rw [R, Lh, gauss_entries]
  congr 1
  refine Matrix.ext fun i j => ?_
  unfold d0
  rw [Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j
  · simpa [mul_smul_comm] using e00
  · simpa using e01
  · simpa using e10
  · simpa using e11
end Formalism.FourierDecayAlt.P.Fr5
