-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_prMu_ph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:01.511618+00:00
-- url     : https://prove2.me/submissions/faa3198d-9acd-4de0-bae7-ce031e0d3c0b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evGL_torus_TMat
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_equiv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (j : CF.J) (nu : Fin n → ℤ) (i : M.ι) (K : TIdx (CF.mu j)) :
    ∑ k, prMu M nu i k * CF.ph j k K = if qb_wtT (CF.mu j) K = nu then CF.ph j i K else 0 := by
  have h := congrArg (evGL (torusPt n)) (qb_equiv_apply CF j i K)
  simp only [map_sum, map_mul, Int.coe_castRingHom, map_intCast,
    qb_evGL_torus_TMat, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true] at h
  have h2 := congrArg (fun x => x.coeff nu) h
  simp only [← zsmul_eq_mul', ← zsmul_eq_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    smul_eq_mul] at h2
  have hp : ∀ i k, prMu M nu i k = (evGL (torusPt n) (M.A i k)).coeff nu := fun _ _ => rfl
  simp only [hp]
  rw [mul_ite, mul_one, mul_zero] at h2
  rw [← h2]
  exact sum_congr rfl fun k _ => mul_comm _ _
end Formalism.InvariantFactorPaths.ColumnFamilies
