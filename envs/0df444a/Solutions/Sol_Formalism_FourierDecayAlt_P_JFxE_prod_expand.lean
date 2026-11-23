-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.prod_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:35.206382+00:00
-- url     : https://prove2.me/submissions/894015a5-787f-4142-99ec-2c6e0842b9fa

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
theorem _root_.solution {X : Type*} [Fintype X] :
    ∀ (t : ℕ) (c : Fin t → X → ℂ) (B : Fin t → X → A),
      (List.ofFn fun j => ∑ x, c j x • B j x).prod =
        ∑ φ : Fin t → X, (∏ j, c j (φ j)) • (List.ofFn fun j => B j (φ j)).prod := by
  intro t
  induction t with
  | zero => intro c B; simp
  | succ t ih =>
    intro c B
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => c j.succ) (fun j => B j.succ), Finset.sum_mul]
    rw [← (Fin.consEquiv fun _ : Fin (t + 1) => X).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ,
      List.prod_cons, smul_mul_smul_comm]
end Formalism.FourierDecayAlt.P.JFxE
