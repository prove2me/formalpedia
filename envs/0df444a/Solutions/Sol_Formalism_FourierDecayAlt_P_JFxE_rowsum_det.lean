-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.rowsum_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:35.328009+00:00
-- url     : https://prove2.me/submissions/683cf16c-381f-4816-9284-7d9e0c7f763b

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
theorem _root_.solution {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (α : Fin t → Fin n) :
    ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, P (α j) (e (σ j)) =
      (Matrix.of fun i j : Fin t => P (α i) (e j)).det := by
  rw [Matrix.det_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin t))) _ _ (fun σ => ?_)
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  congr 1
  exact Fintype.prod_equiv σ _ _ (fun j => by simp)
end Formalism.FourierDecayAlt.P.JFxE
