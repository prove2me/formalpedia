-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.ldu_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:58.753114+00:00
-- url     : https://prove2.me/submissions/038877fc-a68e-4feb-91f5-b50673088e88

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_low_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_up_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_lead_ldu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x7
theorem _root_.solution {r : ℕ} {L U L' U' : Matrix (Fin r) (Fin r) A} {d d' : Fin r → A}
    (hL : IsLowUni L) (hU : IsUpUni U) (hL' : IsLowUni L') (hU' : IsUpUni U')
    (hd : lead (L * Matrix.diagonal d * U) r le_rfl ∈ nonZeroDivisors A)
    (e : L * Matrix.diagonal d * U = L' * Matrix.diagonal d' * U') : L = L' ∧ d = d' ∧ U = U' := by
  rw [lead_ldu d hL hU] at hd
  have hnz : ∀ (i : Fin r) (x : A), x * d i = 0 → x = 0 := by
    intro i x hx
    refine (mem_nonZeroDivisors_iff_right.mp hd) x ?_
    have : (∏ i : Fin r, d (Fin.castLE le_rfl i)) = d i * ∏ j ∈ Finset.univ.erase i, d j :=
      (Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)).symm
    rw [this, ← mul_assoc, hx, zero_mul]
  have uL' : IsUnit L'.det := by rw [isLowUni_det A hL']; exact isUnit_one
  have uU : IsUnit U.det := by rw [isUpUni_det A hU]; exact isUnit_one
  have hP : IsLowUni (L'⁻¹ * L) := isLowUni_mul A (isLowUni_inv A hL') hL
  have hQ : IsUpUni (U' * U⁻¹) := isUpUni_mul A hU' (isUpUni_inv A hU)
  have key : (L'⁻¹ * L) * Matrix.diagonal d = Matrix.diagonal d' * (U' * U⁻¹) := by
    have h1 : L'⁻¹ * (L * Matrix.diagonal d * U) * U⁻¹ = L'⁻¹ * (L' * Matrix.diagonal d' * U') * U⁻¹ := by
      rw [e]
    have h2 : L'⁻¹ * (L * Matrix.diagonal d * U) * U⁻¹ = (L'⁻¹ * L) * Matrix.diagonal d := by
      rw [Matrix.mul_assoc L'⁻¹, Matrix.mul_nonsing_inv_cancel_right _ _ uU, Matrix.mul_assoc]
    have h3 : L'⁻¹ * (L' * Matrix.diagonal d' * U') * U⁻¹ = Matrix.diagonal d' * (U' * U⁻¹) := by
      rw [Matrix.mul_assoc L', Matrix.nonsing_inv_mul_cancel_left _ _ uL', Matrix.mul_assoc]
    rw [← h2, h1, h3]
  have ent : ∀ i j, (L'⁻¹ * L) i j * d j = d' i * (U' * U⁻¹) i j := by
    intro i j
    have := congrFun (congrFun key i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  have hdd : d = d' := by
    funext i
    have := ent i i
    rwa [hP.2, hQ.2, one_mul, mul_one] at this
  have hP1 : L'⁻¹ * L = 1 := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · rw [low_apply hP h, Matrix.one_apply_ne h.ne]
    · subst h; rw [hP.2, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne h.ne']
      refine hnz j _ ?_
      rw [ent, up_apply hQ h, mul_zero]
  have hQ1 : U' * U⁻¹ = 1 := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · rw [Matrix.one_apply_ne h.ne]
      refine hnz i _ ?_
      rw [mul_comm, hdd, ← ent, low_apply hP h, zero_mul]
    · subst h; rw [hQ.2, Matrix.one_apply_eq]
    · rw [up_apply hQ h, Matrix.one_apply_ne h.ne']
  refine ⟨?_, hdd, ?_⟩
  · have := congrArg (L' * ·) hP1
    simpa [Matrix.mul_nonsing_inv_cancel_left _ _ uL'] using this
  · have := congrArg (· * U) hQ1
    simpa [Matrix.nonsing_inv_mul_cancel_right _ _ uU] using this.symm
end Formalism.FourierDecayAlt.P.S3x7
