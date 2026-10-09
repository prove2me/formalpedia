-- Prove2me | solution 1 for BookProof.ChapterF4.hermitian_flow_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:02:27.565055+00:00
-- url     : https://prove2.me/submissions/06cf298b-41ac-42d0-9c68-0bbb25b4ec74

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.hermitian_flow_unitary
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H))ᴴ
        * NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) = 1 := by

  -- By definition of exponentiation, we know that $(e^{i t H})^* = e^{-i t H}$.
  have h_exp_conj : (NormedSpace.exp (-(Complex.I * t) • H))ᴴ = NormedSpace.exp ((Complex.I * t) •
      H) := by
    simp_all only [Matrix.IsHermitian, neg_smul];
    rw [ ← Matrix.exp_conjTranspose ];
    simp [ Matrix.conjTranspose_smul, hH ];
  convert congr_arg₂ ( fun x y => x * y ) h_exp_conj rfl using 1 ; focus (ring);
  focus (congr! 1);
  rw [ ← Matrix.exp_add_of_commute ];
  · norm_num [ ← add_smul ];
  · exact Commute.smul_left ( Commute.smul_right ( Commute.refl _ ) _ ) _
