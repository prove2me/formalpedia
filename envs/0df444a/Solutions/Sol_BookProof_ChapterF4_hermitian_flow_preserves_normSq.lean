-- Prove2me | solution 1 for BookProof.ChapterF4.hermitian_flow_preserves_normSq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:02:52.578525+00:00
-- url     : https://prove2.me/submissions/88b34da7-7864-400c-a4ce-9edaac52427c

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.hermitian_flow_preserves_normSq
import Mathlib
import Definitions.Def_ChapterF4
import Theorems.Thm_BookProof_ChapterF4_hermitian_flow_unitary
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) (c : Fin n → ℂ) :
    star ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)).mulVec c)
          ⬝ᵥ (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)).mulVec c
      = star c ⬝ᵥ c := by

  have hU : (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H))ᴴ * NormedSpace.exp ((-Complex.I * (t :
      ℂ)) • H) = 1 := by
    convert hermitian_flow_unitary H hH t using 1;
  have hstar : star (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) *ᵥ c) = star c ᵥ* (NormedSpace.exp
      ((-Complex.I * (t : ℂ)) • H))ᴴ := by
    ext i; simp [ Matrix.mulVec, dotProduct ] ;
    simp [ Matrix.vecMul, dotProduct, mul_comm ];
  simp_all [ Matrix.dotProduct_mulVec ]
