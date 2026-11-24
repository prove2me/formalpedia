-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_colFam_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:58:49.034922+00:00
-- url     : https://prove2.me/submissions/c0bd2e7d-6016-4c07-a1d2-a15db4cb88be

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_dMu_sh
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_TMat_sh
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_dom_sh
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_indep_tw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (M M' : GLMod n) (ε : ℤ) (e : M'.ι ≃ M.ι)
    (hA : ∀ i j, M'.A i j = ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * M.A (e i) (e j))
    (CF : ColFam M) : Nonempty (ColFam M') := by
  refine ⟨{ J := CF.J, mu := fun j => qc_sh (CF.mu j) ε, dom := fun j => qc_dom_sh (CF.dom j) ε,
            ph := fun j => fun i' I' => CF.ph j (e i') (qc_idxE (CF.mu j) ε I'),
            equiv := ?_, indepP := ?_, indepQ := ?_, rank := ?_ }⟩
  · intro j
    ext i' I'
    have h : ∑ k, M.A (e i') k * (Int.castRingHom (GLCoord ℤ n)) (CF.ph j k (qc_idxE (CF.mu j) ε I')) =
        ∑ K, (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e i') K) * TMat (CF.mu j) K (qc_idxE (CF.mu j) ε I') :=
      congrFun (congrFun (CF.equiv j) (e i')) (qc_idxE (CF.mu j) ε I')
    show ∑ k', M'.A i' k' * (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e k') (qc_idxE (CF.mu j) ε I')) =
      ∑ K', (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e i') (qc_idxE (CF.mu j) ε K')) *
        TMat (qc_sh (CF.mu j) ε) K' I'
    simp only [hA, qc_TMat_sh]
    rw [Equiv.sum_comp e (fun k => ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * M.A (e i') k *
        (Int.castRingHom (GLCoord ℤ n)) (CF.ph j k (qc_idxE (CF.mu j) ε I'))),
      Equiv.sum_comp (qc_idxE (CF.mu j) ε) (fun K => (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e i') K) *
        (((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * TMat (CF.mu j) K (qc_idxE (CF.mu j) ε I')))]
    simp only [mul_assoc, mul_left_comm _ ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n), ← Finset.mul_sum]
    rw [h]
  · intro p hp nu
    exact qc_indep_tw CF e ε (CF.indepP p hp) nu
  · intro nu
    exact qc_indep_tw CF e ε CF.indepQ nu
  · rw [Fintype.card_congr e, CF.rank]
    exact Finset.sum_congr rfl fun j _ => (qc_dMu_sh (CF.mu j) ε).symm
end Formalism.InvariantFactorPaths.ColumnFamilies
