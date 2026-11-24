-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:05:32.723359+00:00
-- url     : https://prove2.me/submissions/07baab18-5698-48f0-99a6-36b39eeed470

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_key_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_key_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_vecF_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (nu : Fin n → ℤ)
    (hmax : ∀ y, a y ≠ 0 → DomLE nu (CF.mu y.1) → CF.mu y.1 = nu) (i : M.ι) :
    qb_ev M ℚ nu (∑ y, a y • qb_vecF CF ℚ y) i =
      ∑ j : {j : CF.J // CF.mu j = nu}, ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : ℚ) • qd_f CF a j.1 := by
  classical
  rw [← qb_evL_apply, map_sum, Finset.sum_apply, Fintype.sum_sigma,
    ← Finset.sum_subtype (univ.filter fun j => CF.mu j = nu) (by simp)
      (fun j => ((CF.ph j i (canT (CF.mu j)) : ℤ) : ℚ) • qd_f CF a j), Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · subst hj
    rw [qd_f, Finset.smul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, Pi.smul_apply, qb_evL_apply, qb_vecF_def, qb_key_eq, smul_comm, Algebra.smul_def (R := ℚ)
      ((CF.ph j i (canT (CF.mu j)) : ℤ) : ℚ), map_intCast]
  · refine Finset.sum_eq_zero fun I _ => ?_
    rw [map_smul, Pi.smul_apply, qb_evL_apply, qb_vecF_def]
    by_cases ha : a ⟨j, I⟩ = 0
    · rw [ha, zero_smul]
    · rw [qb_key_zero CF ℚ j I.1 nu (fun hd => hj (hmax ⟨j, I⟩ ha hd)), Pi.zero_apply, smul_zero]
end Formalism.InvariantFactorPaths.ColumnFamilies
