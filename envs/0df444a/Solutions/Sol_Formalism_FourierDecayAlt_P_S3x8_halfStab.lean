-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.halfStab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:37.951152+00:00
-- url     : https://prove2.me/submissions/8f755c81-550c-4178-9339-47e1453770a6

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_uniqCm
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_det_of_cm
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block21_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_lcancel
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_rcancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {F : Type} [Field F] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {g n n' : Matrix (Idx r k) (Idx r k) F}
    (hc : ∀ (l : ℕ) (hl : l ≤ r), cm (b31 g) l hl ≠ 0) (hn : IsN n) (hn' : IsN n')
    (e : g * n' = n * g) : b33 n = 1 ∧ b11 n' = 1 ∧ b23 n = 0 ∧ b12 n' = 0 := by
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  obtain ⟨g11, g33, g22, g21, g31, g32⟩ := hn'
  have hu : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm (b31 g) l hl) := fun l hl => (hc l hl).isUnit
  have hd : IsUnit (b31 g).det := det_of_cm _ (hu r le_rfl)
  have e31 := congrArg b31 e
  rw [block31_mul, block31_mul, g21, g31, h31, h32] at e31
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e31
  obtain ⟨u2, u1⟩ := uniqCm (b31 g) (b33 n) (b11 n') h33 g11 e31.symm hu
  refine ⟨u2, u1, ?_, ?_⟩
  · have e21 := congrArg b21 e
    rw [block21_mul, block21_mul, g21, g31, h21, h22, u1] at e21
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul] at e21
    refine rcancel hd ?_
    rw [Matrix.zero_mul]
    exact (left_eq_add.1 e21)
  · have e32 := congrArg b32 e
    rw [block32_mul, block32_mul, g22, g32, h31, h32, u2] at e32
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul] at e32
    refine lcancel hd ?_
    rw [Matrix.mul_zero]
    exact (add_eq_right.1 e32)
end Formalism.FourierDecayAlt.P.S3x8
