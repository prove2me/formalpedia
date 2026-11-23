-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.degreeOf_prod_linear_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:51.815867+00:00
-- url     : https://prove2.me/submissions/2edc5322-fc24-4bd6-affc-ef2278b303c0

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open MvPolynomial
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (N n : ℕ) (lam : Fin n → ℝ) (c : ℝ) (a : Fin N) :
    (C c * ∏ b : Fin N, ∏ s : Fin n, (X b + C (lam s)) : MvPolynomial (Fin N) ℝ).degreeOf a ≤ n := by
  classical
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [degreeOf_C, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  have h1 : ∀ b : Fin N, degreeOf a (∏ s : Fin n, (X b + C (lam s)) : MvPolynomial (Fin N) ℝ) ≤ if a = b then n else 0 := by
    intro b
    refine (degreeOf_prod_le _ _ _).trans ?_
    have h2 : ∀ s : Fin n, degreeOf a (X b + C (lam s) : MvPolynomial (Fin N) ℝ) ≤ if a = b then 1 else 0 := by
      intro s
      refine (degreeOf_add_le _ _ _).trans ?_
      rw [degreeOf_C, degreeOf_X]
      simp
    refine (Finset.sum_le_sum fun s _ => h2 s).trans ?_
    split_ifs <;> simp
  refine (Finset.sum_le_sum fun b _ => h1 b).trans ?_
  simp
end Formalism.FourierDecayAlt.P.LEx2
