-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.det_rows_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:14.572685+00:00
-- url     : https://prove2.me/submissions/0e33cd53-bb6f-4664-821d-8c1a6a3025f3

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (γ : Equiv.Perm (Fin t)) :
    (Matrix.of fun i j : Fin t => P (e (γ i)) (e j)).det = ((Equiv.Perm.sign γ : ℤ) : ℂ) * P.det := by
  have : (Matrix.of fun i j : Fin t => P (e (γ i)) (e j)) = (P.submatrix e e).submatrix γ id := by
    ext i j; simp
  rw [this, Matrix.det_permute, Matrix.det_submatrix_equiv_self]
end Formalism.FourierDecayAlt.P.JFxE
