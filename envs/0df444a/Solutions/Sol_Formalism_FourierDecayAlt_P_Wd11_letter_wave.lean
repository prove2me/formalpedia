-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.letter_wave
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:09:34.611196+00:00
-- url     : https://prove2.me/submissions/1315aa60-6958-40d0-8d33-cfdbcaae1038

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_comm_of_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_Tm_map_star
import Theorems.Thm_Formalism_YangianSpanCharacter_Final_T_PlaneWave
import Theorems.Thm_Formalism_YangianSpanCharacter_P_comm_of_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution (σ : Site A) (f fi : A) (s : K) (l : Letter K S)
    (hW : IsWave f fi) (hc : f * σ.c = σ.c * f) (hci : f * σ.ci = σ.ci * f)
    (hp : σ.p * f = f * σ.p + algebraMap K A s * f * σ.c) :
    (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) * Matrix.diagonal (fun _ => f) *
        Uinv (if l.plus then s else star s) =
      Matrix.diagonal (fun _ => f) * (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) := by
  obtain ⟨h1, h2, h3⟩ := hW
  by_cases hl : l.plus
  · simp only [hl, if_true]
    exact (Formalism.YangianSpanCharacter.Final.T_PlaneWave K A σ.p σ.c σ.ci f s l.pt hc hci hp).2.2
  · simp only [hl, Bool.false_eq_true, if_false]
    unfold Ts
    rw [Tm_map_star]
    refine (Formalism.YangianSpanCharacter.Final.T_PlaneWave K A (star σ.p) (star σ.c) (star σ.ci) f (star s) (star l.pt)
      ?_ ?_ ?_).2.2
    · refine comm_of_inv h1 h2 ?_
      have := congrArg star hc
      rw [star_mul, star_mul, h3] at this
      exact this
    · refine comm_of_inv h1 h2 ?_
      have := congrArg star hci
      rw [star_mul, star_mul, h3] at this
      exact this
    · have hs := congrArg star hp
      rw [star_mul, star_add, star_mul, star_mul, star_mul, h3, ← algebraMap_star_comm] at hs
      have hz : ∀ x : A, algebraMap K A (star s) * x = x * algebraMap K A (star s) :=
        fun x => Algebra.commutes _ x
      calc star σ.p * f = f * (fi * star σ.p) * f := by
            rw [← mul_assoc, h1, one_mul]
        _ = f * star σ.p * (fi * f) + f * star σ.c * (fi * f) * algebraMap K A (star s) := by
            rw [hs, mul_add, add_mul]
            congr 1
            · simp only [mul_assoc]
            · simp only [mul_assoc]
              rw [hz f]
        _ = f * star σ.p + algebraMap K A (star s) * f * star σ.c := by
            rw [h2, mul_one, mul_one, mul_assoc (algebraMap K A (star s)), hz]
end Formalism.FourierDecayAlt.P.Wd11
