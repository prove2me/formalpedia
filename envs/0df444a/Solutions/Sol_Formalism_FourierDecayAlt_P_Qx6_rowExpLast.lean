-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.rowExpLast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:37:51.068409+00:00
-- url     : https://prove2.me/submissions/7ec5e949-bd79-494b-9fc7-6fda7f901732

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_REAL_cycleToLast_castSucc
import Theorems.Thm_Formalism_REAL_cycleToLast_last
import Theorems.Thm_Formalism_REAL_extendLast_castSucc
import Theorems.Thm_Formalism_REAL_extendLast_last
import Theorems.Thm_Formalism_REAL_lastColumnSplit_bijective
import Theorems.Thm_Formalism_REAL_sign_cycleToLast
import Theorems.Thm_Formalism_REAL_sign_extendLast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
        (qminorRow E (a ∘ Fin.castSucc) (b ∘ l.succAbove) (u - 1) * Tm E u (a (Fin.last t)) (b l)) := by
  unfold qminorRow
  rw [(Fintype.sum_bijective _ (lastColumnSplit_bijective t) _ _ (fun _ => rfl)).symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
  simp only [lastColumnSplit, Equiv.Perm.sign_mul, sign_cycleToLast, sign_extendLast, Equiv.Perm.mul_apply,
    extendLast_castSucc, cycleToLast_castSucc, extendLast_last, cycleToLast_last, Fin.val_castSucc, Fin.val_last,
    Function.comp]
  have e1 : u - ((t + 1 : ℕ) : ℂ) + 1 + (t : ℂ) = u := by push_cast; ring
  have e2 : ∀ i : Fin t, u - ((t + 1 : ℕ) : ℂ) + 1 + ((i : ℕ) : ℂ) = u - 1 - (t : ℂ) + 1 + ((i : ℕ) : ℂ) := by
    intro i; push_cast; ring
  simp only [e1, e2]
  have hj : (j : ℕ) ≤ t := Nat.lt_succ_iff.mp j.isLt
  have hs : (-1 : ℤ) ^ (t + (j : ℕ)) = (-1) ^ (t - (j : ℕ)) := by
    rw [show t + (j : ℕ) = (t - (j : ℕ)) + 2 * (j : ℕ) by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  rw [hs]
  push_cast
  simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Qx6
