-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.PhiH_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:45.778745+00:00
-- url     : https://prove2.me/submissions/43b009a9-e92f-4433-abb0-7667a5e73e21

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_blkM_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_mem_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_blkM_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] (R : Subring K)
variable {a s : ℕ}
variable {N : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (ψ : AddChar K ℂ) (h : Point K) {n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) (s : ℕ) (Z : Matrix (Fin s) (Fin s) K)
    (hne : PhiH R ψ h Z' s Z ≠ 0) (i j : Fin s) :
    ∃ r ∈ R, Z i j = Ring.inverse (pt h.1 h.2).det * r := by
  by_contra hcon
  push_neg at hcon
  apply hne
  unfold PhiH
  apply finsum_eq_zero_of_forall_eq_zero
  intro τ
  suffices hF : Fz R Z' (bigZ rfl (orbZ h (rep R τ.1)) (outM R τ.2.1) (outM R τ.2.2) Z) = 0 by
    rw [hF, zero_mul]
  unfold Fz
  rw [if_neg]
  intro hI
  obtain ⟨hT, hTY, hXT, hD⟩ := (blkM_isInt rfl _ _ _ _ R).1 hI
  set T := orbZ h (rep R τ.1) with hTdef
  set X := outM R τ.2.1
  set Y := outM R τ.2.2
  have hdT : T.det = (pt h.1 h.2).det := by
    rw [hTdef]
    unfold orbZ
    rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det K (rep R τ.1).1.2.1, isUpUni_det K (rep R τ.1).2.2]
    ring
  have hu : IsUnit T.det := by
    rw [hdT]
    exact pt_unit_lemma_5 h.1 h.2
  have hTR : T = R.subtype.mapMatrix (Matrix.of fun a b => (⟨T a b, hT a b⟩ : R)) := by
    ext a b
    rfl
  have hadj : IsInt R T.adjugate := by
    rw [hTR, ← RingHom.map_adjugate]
    intro a b
    exact ((Matrix.adjugate (Matrix.of fun a b => (⟨T a b, hT a b⟩ : R))) a b).2
  have hdet : T.det ∈ R := by
    rw [hTR, ← RingHom.map_det]
    exact (Matrix.det (Matrix.of fun a b => (⟨T a b, hT a b⟩ : R))).2
  have hXTY : X * T * Y = Ring.inverse T.det • (X * T * T.adjugate * (T * Y)) := by
    have e1 : X * T * Y = X * T * T⁻¹ * (T * Y) := by
      rw [Matrix.mul_assoc (X * T), ← Matrix.mul_assoc T⁻¹, Matrix.nonsing_inv_mul T hu, Matrix.one_mul]
    rw [e1, Matrix.inv_def, Matrix.mul_smul, Matrix.smul_mul]
  have hm : ((X * T) * T.adjugate * (T * Y)) i j ∈ R :=
    mem_mul R (mem_mul R hXT hadj) hTY i j
  apply hcon (T.det * (X * T * Y + Z) i j - ((X * T) * T.adjugate * (T * Y)) i j)
    (R.sub_mem (R.mul_mem hdet (hD i j)) hm)
  rw [mul_sub, ← mul_assoc, ← hdT, Ring.inverse_mul_cancel _ hu, one_mul, Matrix.add_apply, hXTY,
    Matrix.smul_apply, smul_eq_mul]
  ring
end Formalism.FourierDecayAlt.P.TwoBlockPoint
