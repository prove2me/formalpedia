-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.two_formal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:44:09.125825+00:00
-- url     : https://prove2.me/submissions/0be92e0e-b6df-445b-847e-e37f9cb9fdaf

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Theorems.Thm_Formalism_REAL_ite_zero_eq_ite_smul
import Theorems.Thm_Formalism_REAL_ite_zero_eq_mul_ite
import Theorems.Thm_Formalism_REAL_shiftedGenerator_eq_ite_smul_add


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
theorem _root_.solution (E : Fin n → Fin n → A) (x y : ℂ) (hxy : x - y = 1) (p q c d : Fin n) :
    Tm E x p c * Tm E y q d - Tm E x q c * Tm E y p d + Tm E x p d * Tm E y q c
      - Tm E x q d * Tm E y p c = rel E p c q d + rel E p d q c := by
  obtain rfl : y = x - 1 := by linear_combination -hxy
  unfold rel
  simp only [eq_comm (a := c) (b := q), eq_comm (a := d) (b := p), eq_comm (a := d) (b := q),
    eq_comm (a := c) (b := p)]
  rw [ite_zero_eq_ite_smul (q = c) (E p d), ite_zero_eq_ite_smul (p = d) (E q c), ite_zero_eq_ite_smul (q = d) (E p c), ite_zero_eq_ite_smul (p = c) (E q d)]
  simp only [shiftedGenerator_eq_ite_smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [ite_zero_eq_mul_ite (p = c) x, ite_zero_eq_mul_ite (q = d) (x - 1), ite_zero_eq_mul_ite (q = c) x, ite_zero_eq_mul_ite (p = d) (x - 1),
    ite_zero_eq_mul_ite (p = d) x, ite_zero_eq_mul_ite (q = c) (x - 1), ite_zero_eq_mul_ite (q = d) x, ite_zero_eq_mul_ite (p = c) (x - 1)]
  module
end Formalism.FourierDecayAlt.P.JFxE
