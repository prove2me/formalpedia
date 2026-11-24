-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_wtT_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:26.080316+00:00
-- url     : https://prove2.me/submissions/ef89c58a-4d3f-4c9c-b348-ea206a2183e7

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_sum_wtT
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_col_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_col_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_wtT_can

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
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) : qb_wtT mu I = mu ↔ I = canT mu := by
  constructor
  · intro h
    funext c
    apply Subtype.ext
    apply qb_col_eq mu c (I c).1 (I c).2
    intro a
    have h1 : ∑ b ∈ univ.filter (· ≤ a), qb_wtT mu I b = ∑ b ∈ univ.filter (· ≤ a), qb_wtT mu (canT mu) b := by
      rw [h, qb_wtT_can hmu]
    rw [qb_sum_wtT, qb_sum_wtT] at h1
    have h2 : ∑ c : ↥(TCols mu), ((((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) -
        (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ)) = 0 := by
      rw [sum_sub_distrib]; linarith
    have h3 := (sum_eq_zero_iff_of_nonneg (fun c _ => by
      have := qb_col_le mu c (I c).1 (I c).2 a
      have : (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) ≤
        (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) := by exact_mod_cast this
      linarith)).1 h2 c (mem_univ c)
    have : (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) =
        (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) := by linarith
    exact_mod_cast this
  · rintro rfl; exact qb_wtT_can hmu
end Formalism.InvariantFactorPaths.ColumnFamilies
