-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.Tm_Ead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:14.32092+00:00
-- url     : https://prove2.me/submissions/c3390ba2-7188-4803-befc-4b100b981df1

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
theorem _root_.solution (E : Fin n → Fin n → A) {P Q : Matrix (Fin n) (Fin n) ℂ} (hQP : Q * P = 1) (v : ℂ) (c d : Fin n) :
    Tm (Ead E P Q) v c d = ∑ a, ∑ b, (P a c * Q d b) • Tm E v a b := by
  have h1 : ∀ a, ∑ b, (P a c * Q d b) • (if a = b then algebraMap ℂ A v else 0) =
      (P a c * Q d a) • algebraMap ℂ A v := by
    intro a; simp [smul_ite]
  have h2 : ∑ a, P a c * Q d a = if c = d then 1 else 0 := by
    have := congrFun (congrFun hQP d) c
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    rw [show (∑ a, P a c * Q d a) = ∑ a, Q d a * P a c from Finset.sum_congr rfl fun a _ => mul_comm _ _, this]
    simp [eq_comm]
  unfold Tm Ead
  simp only [smul_add, Finset.sum_add_distrib, h1]
  rw [← Finset.sum_smul, h2]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.JFxE
