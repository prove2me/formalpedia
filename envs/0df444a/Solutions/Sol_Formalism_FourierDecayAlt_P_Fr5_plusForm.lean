-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.plusForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:59.475558+00:00
-- url     : https://prove2.me/submissions/97377238-51c8-469e-a4d3-d18d9cde3a1b

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_comm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_io_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_freeOf2_of_four_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_diag_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_fn_comm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem___d82dc59c5260
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem__i_7172e6a0b2cd
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem__b_4a242cf5d7ab
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_mem__bi_956546b22979
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_mem_GG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_mem_GGi
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_star__i_3a44bc578970
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_star__bi_ef3e65c928e2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_star_GG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_comm_wt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_io_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_wt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_free_d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_gaussFormPlus
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_w1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_w2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_diag_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_insert_diagonal_extract
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_ins_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
namespace Formalism.FourierDecayAlt.P.Fr5
section Core
variable {B : Type} [Ring B] [StarRing B] [Algebra ℂ B]
end Core
section Slots
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
private lemma d0_eq_diagonal (b : SlopeTestRemainingChoices S A) : d0 b = !![b, 0; 0, b] := by
  first
  | (refine Matrix.ext fun i j => ?_
     fin_cases i <;> fin_cases j <;> rfl)
  | (refine Matrix.ext fun i j => ?_
     fin_cases i <;> fin_cases j <;> simp [d0])
end Slots
section Level
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
end Level
section Main
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
end Main
end Formalism.FourierDecayAlt.P.Fr5
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr5
theorem _root_.solution (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ) (H : PlusHyp L f a Ya) :
    (f.plus L a Ya).RR = star (f.plus L a Ya).F * (f.plus L a Ya).d L * (f.plus L a Ya).F := by
  have hG := gaussFormPlus L f a Ya H
  have hfree0 := H.2.2.1
  obtain ⟨hs, hf, hfree, hY, hYi, hY1i, -⟩ := H
  obtain ⟨-, -, -, -, fx, fxi, fc, -, -⟩ := hfree0
  obtain ⟨hx1, hx1'⟩ := hf.x_xi (Ya + 1) hY1i
  have hd : f.d L = (wt L : SlopeTestRemainingChoices S A) ^ f.N * f.c := rfl
  have gW : ∀ g ∈ zfns L, Commute (io g : SlopeTestRemainingChoices S A) (wt L) := fun g hg => comm_wt L (io_fn_comm L hg)
  have gc : ∀ g ∈ zfns L, Commute (io g : SlopeTestRemainingChoices S A) f.c := fun g hg => (hf.c_fn g hg).symm
  have cW : Commute f.c (wt L : SlopeTestRemainingChoices S A) := comm_wt L hf.c_fn
  have xiζi : Commute (f.xi (Ya + 1)) (io L.ζi) := comm_inv hx1 hx1' (hf.x_fn (Ya + 1) _ (mem_ζi L))
  have xζbi : Commute (f.x Ya) (io L.ζbi) := hf.x_fn Ya _ (mem_ζbi L)
  have xG : Commute (f.x Ya) (io L.GG) := hf.x_fn Ya _ (mem_GG L)
  have cb1 : Commute L.ζbi L.ζ := fn_comm L (mem_ζbi L) (mem_ζ L)
  have cb2 : Commute L.ζbi L.ζb := fn_comm L (mem_ζbi L) (mem_ζb L)
  have cb3 : Commute L.ζbi L.GGi := fn_comm L (mem_ζbi L) (mem_GGi L)
  have k1 : L.ζ * L.ζb * L.GGi * L.ζbi * L.ζi = L.GGi := by
    rw [← ((cb1.mul_right cb2).mul_right cb3).eq]
    exact w1 L
  have hw : (wt L : SlopeTestRemainingChoices S A) * io L.ζbi * io L.ζi = io L.GGi := by
    show (io (L.ζ * L.ζb * L.GGi) : SlopeTestRemainingChoices S A) * io L.ζbi * io L.ζi = io L.GGi
    rw [← io_mul, ← io_mul, k1]
  have hw2 : (io L.GG : SlopeTestRemainingChoices S A) * (io L.ζi * (wt L * (io L.ζbi * io L.GG))) = io L.GG := by
    show (io L.GG : SlopeTestRemainingChoices S A) * (io L.ζi * (io (L.ζ * L.ζb * L.GGi) * (io L.ζbi * io L.GG))) = io L.GG
    rw [← io_mul, ← io_mul, ← io_mul, ← io_mul]
    congr 1
    rw [← mul_assoc L.GG L.ζi, ← mul_assoc (L.GG * L.ζi)]
    exact w2 L
  have E1 : io L.ζbi * (wt L ^ (f.N + 1) * f.c) * (f.q Ya • f.xi (Ya + 1)) * io L.ζi =
      f.d L * (f.q Ya • (io L.GGi * f.xi (Ya + 1))) := by
    rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [hd, pow_succ]
    simp only [mul_assoc]
    rw [((gW _ (mem_ζbi L)).pow_right f.N).left_comm, (gW _ (mem_ζbi L)).left_comm,
      (gc _ (mem_ζbi L)).left_comm, cW.symm.left_comm, xiζi.eq]
    rw [← mul_assoc (io L.ζbi) (io L.ζi) (f.xi (Ya + 1)),
      ← mul_assoc (wt L) (io L.ζbi * io L.ζi) (f.xi (Ya + 1)), ← mul_assoc (wt L) (io L.ζbi) (io L.ζi), hw]
  have E2 : io L.GG * io L.ζi * (wt L ^ (f.N + 1) * f.c) * f.x Ya * (io L.ζbi * io L.GG) =
      f.d L * (io L.GG * f.x Ya) := by
    rw [hd, pow_succ]
    simp only [mul_assoc]
    rw [xζbi.left_comm, xG.eq]
    rw [((gW _ (mem_ζi L)).pow_right f.N).left_comm, ((gW _ (mem_GG L)).pow_right f.N).left_comm]
    rw [cW.symm.left_comm, (gc _ (mem_ζi L)).left_comm, (gc _ (mem_GG L)).left_comm]
    rw [← mul_assoc (io L.ζbi) (io L.GG) (f.x Ya), ← mul_assoc (wt L) (io L.ζbi * io L.GG) (f.x Ya),
      ← mul_assoc (io L.ζi) (wt L * (io L.ζbi * io L.GG)) (f.x Ya),
      ← mul_assoc (io L.GG) (io L.ζi * (wt L * (io L.ζbi * io L.GG))) (f.x Ya), hw2]
  have fd : FreeOf a (f.d L) := free_d L f hfree
  have fX : FreeOf a ((wt L : SlopeTestRemainingChoices S A) ^ (f.N + 1) * f.c) := free_mul (free_pow (free_wt L a) _) fc
  have fd0 : ∀ X : SlopeTestRemainingChoices S A, FreeOf a X → FreeOf2 a (d0 X) := fun X hX => by
    rw [d0_eq_diagonal]; exact freeOf2_of_four_entries hX (free_zero a) (free_zero a) hX
  have fZ2 : FreeOf2 a !![(io L.ζi : SlopeTestRemainingChoices S A), 0; 0, io L.ζbi * io L.GG] :=
    freeOf2_of_four_entries (free_io a _) (free_zero a) (free_zero a) (free_mul (free_io a _) (free_io a _))
  have fZh : FreeOf2 a !![(io L.ζbi : SlopeTestRemainingChoices S A), 0; 0, io L.GG * io L.ζi] :=
    freeOf2_of_four_entries (free_io a _) (free_zero a) (free_zero a) (free_mul (free_io a _) (free_io a _))
  have fC : FreeOf2 a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya] :=
    freeOf2_of_four_entries (free_smul _ (fxi _)) (free_zero a) (free_zero a) (fx _)
  have key : ins a !![(io L.ζbi : SlopeTestRemainingChoices S A), 0; 0, io L.GG * io L.ζi] *
      (wt L ^ (f.N + 1) * (f.c * ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya])) *
      ins a !![io L.ζi, 0; 0, io L.ζbi * io L.GG] =
      f.d L * ins a !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya] := by
    rw [← mul_assoc ((wt L : SlopeTestRemainingChoices S A) ^ (f.N + 1)) f.c, ← Wd1.insert_diagonal_extract a ((wt L : SlopeTestRemainingChoices S A) ^ (f.N + 1) * f.c),
      ← Wd1.insert_diagonal_extract a (f.d L)]
    simp only [mul_assoc]
    rw [← Wd1.ins_mul a _ _ fC, ← Wd1.ins_mul a _ _ (fd0 _ fX), ← Wd1.ins_mul a _ _ fZh,
      ← Wd1.ins_mul a _ _ (fd0 _ fd)]
    congr 1
    simp only [← mul_assoc]
    rw [diag_entries, d0_eq_diagonal, Matrix.mul_fin_two]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    rw [E1, E2]
  have key' : ∀ Y : SlopeTestRemainingChoices S A, ins a !![(io L.ζbi : SlopeTestRemainingChoices S A), 0; 0, io L.GG * io L.ζi] *
      (wt L ^ (f.N + 1) * (f.c * (ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya] *
      (ins a !![io L.ζi, 0; 0, io L.ζbi * io L.GG] * Y)))) =
      f.d L * (ins a !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya] * Y) := by
    intro Y
    have e := congrArg (· * Y) key
    simp only [mul_assoc] at e
    exact e
  have hZ : (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * f.l L Ya, io L.GG] : M2 (SlopeTestRemainingChoices S A)) =
      !![io L.ζi, 0; 0, io L.ζbi * io L.GG] * !![1, 0; f.l L Ya, 1] := by
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp only [mul_one, mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_assoc]
  show f.RR * ins a (f.TT Ya) =
    star (ins a (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * f.l L Ya, io L.GG]) * f.F) *
      ((wt L : SlopeTestRemainingChoices S A) ^ (f.N + 1) * (f.c * ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya])) *
      (ins a (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * f.l L Ya, io L.GG]) * f.F)
  rw [hG, hZ, Wd1.ins_mul a _ _ fZ2, star_mul, star_mul, star_mul, Wd1.ins_star a _ fZ2, diag_conj,
    io_star, star_mul, io_star, io_star, star_ζi hs, star_GG hs, star_ζbi hs]
  simp only [mul_assoc]
  rw [key']
end Formalism.FourierDecayAlt.P.Fr5
