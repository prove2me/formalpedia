-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.cplx_str_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:15:57.930943+00:00
-- url     : https://prove2.me/submissions/9f22b004-d544-4461-913a-fc94f506cd4c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {m : Type} [Fintype m] [DecidableEq m]
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (H P Q J : Matrix m m ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hJ2 : J * J = 1) (hJh : Jᴴ = J) (hH : Pᴴ * H * P = J) :
    let K := P * (Complex.I • J) * Q
    (K * K = -1) ∧ (Kᴴ * H * K = H) ∧ (Kᴴ * H = (-Complex.I) • (Qᴴ * Q)) ∧
      K.trace = Complex.I * J.trace := by
  dsimp only
  have hQP' : ∀ X : Matrix m m ℂ, Q * (P * X) = X := fun X => by rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hJ2' : ∀ X : Matrix m m ℂ, J * (J * X) = X := fun X => by rw [← Matrix.mul_assoc, hJ2, Matrix.one_mul]
  have hPQh' : ∀ X : Matrix m m ℂ, Pᴴ * (Qᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hQP, Matrix.conjTranspose_one, Matrix.one_mul]

  have hH' : H = Qᴴ * (J * Q) := by
    have hq : Qᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
    calc H = (Qᴴ * Pᴴ) * H * (P * Q) := by rw [hq, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = Qᴴ * ((Pᴴ * H * P) * Q) := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (J * Q) := by rw [hH]
  have hsI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, hQP', hJ2', hPQ, Complex.I_mul_I,
      neg_smul, one_smul]
  · rw [hH']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hJh, hsI, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, Matrix.mul_assoc, hQP', hJ2', hPQh']
    rw [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  · rw [hH']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hJh, hsI, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, Matrix.mul_assoc, hQP', hJ2', hPQh']
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
end Formalism.L2.Pj.DatLin
