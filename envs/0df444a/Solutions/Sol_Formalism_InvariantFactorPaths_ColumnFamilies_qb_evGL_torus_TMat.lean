-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_evGL_torus_TMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:57:02.979177+00:00
-- url     : https://prove2.me/submissions/7ff3182b-27dd-4388-a536-fd4032045956

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evGL_minorC
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evGL_detU_zpow
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_minor_diagonal
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_prod_single
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_sU_val
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_sU_zpow

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
theorem _root_.solution (mu : Fin n → ℤ) (J I : TIdx mu) :
    evGL (torusPt n) (TMat mu J I) = if J = I then AddMonoidAlgebra.single (qb_wtT mu I) 1 else 0 := by
  unfold TMat
  rw [map_mul, map_prod]
  have hdet : ((qb_sU (∑ a : Fin n, Pi.single a (1 : ℤ)) : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ) :
      AddMonoidAlgebra ℤ (Fin n → ℤ)) = (torusPt n).val.det := by
    rw [qb_sU_val]
    change _ = Matrix.det (Matrix.diagonal _)
    rw [Matrix.det_diagonal, qb_prod_single]
  rw [qb_evGL_detU_zpow (torusPt n) _ hdet, qb_sU_zpow, qb_sU_val]
  have hm : ∀ c : ↥(TCols mu), evGL (torusPt n) (minorC (J c).1 (I c).1 (J c).2 (I c).2) =
      if (J c).1 = (I c).1 then AddMonoidAlgebra.single (∑ x ∈ (J c).1, Pi.single x (1 : ℤ)) 1 else 0 := by
    intro c
    rw [qb_evGL_minorC]
    change Matrix.det (Matrix.of fun a b => Matrix.diagonal _ _ _) = _
    rw [qb_minor_diagonal, qb_prod_single]
  simp only [hm]
  split_ifs with hJI
  · subst hJI
    simp only [if_true]
    rw [qb_prod_single, AddMonoidAlgebra.single_mul_single, one_mul]
    congr 1
    funext a
    simp only [qb_wtT, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Pi.single_apply, card_filter,
      Nat.cast_sum, smul_eq_mul]
    simp
  · have : ∃ c, (J c).1 ≠ (I c).1 := by
      by_contra hc
      push Not at hc
      exact hJI (funext fun c => Subtype.ext (hc c))
    obtain ⟨c, hc⟩ := this
    rw [prod_eq_zero (mem_univ c) (if_neg hc), mul_zero]
end Formalism.InvariantFactorPaths.ColumnFamilies
