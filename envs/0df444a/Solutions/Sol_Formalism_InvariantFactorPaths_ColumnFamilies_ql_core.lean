-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:22:13.453697+00:00
-- url     : https://prove2.me/submissions/f9e6cc86-86ac-4fa2-a5be-0140aff400bd

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_E_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_P_cast
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_P_equiv
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_TMat
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sum_L
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_minorC_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_sum_indices_eq_sum_columns


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
theorem _root_.solution (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) {lo : ℤ} {N : ℕ}
    (m1 : lo ≤ mu (lastIdx n)) (m2 : mu 0 ≤ lo + N) (n1 : lo ≤ nu (lastIdx n)) (n2 : nu 0 ≤ lo + N)
    (K : TIdx mu) (L : LamIdx n b) (I : TIdx nu) :
    ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) *
        ((ql_P ℤ (ql_E lo N (qs_ext mu y.1)) y.2.1 (ql_E lo N (qs_ext nu I)) : ℤ) : GLCoord ℤ n) =
      ∑ I' : TIdx nu, ((ql_P ℤ (ql_E lo N (qs_ext mu K)) L.1 (ql_E lo N (qs_ext nu I')) : ℤ) : GLCoord ℤ n) *
        TMat nu I' I := by
  set d : GLCoord ℤ n := ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) with hd
  set k := ql_E lo N (qs_ext mu K) with hk
  set i := ql_E lo N (qs_ext nu I) with hi
  calc ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) *
        ((ql_P ℤ (ql_E lo N (qs_ext mu y.1)) y.2.1 i : ℤ) : GLCoord ℤ n)
      = ∑ K' : TIdx mu, ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (ql_E lo N (qs_ext mu K') j)) *
          qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) (ql_E lo N (qs_ext mu K')) L'.1 i) := by
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun K' _ => sum_congr rfl fun L' _ => ?_
        rw [ql_TMat hmu m1 m2, LamMat, qs_minorC_eq, ql_P_cast]; ring
    _ = ∑ k' : Fin N → Finset (Fin n), ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) k' L'.1 i) := by
        refine sum_indices_eq_sum_columns hmu m1 m2 (fun k' => ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) k' L'.1 i)) ?_
        rintro f ⟨j, hj⟩
        refine sum_eq_zero fun L' _ => ?_
        rw [prod_eq_zero (mem_univ j) (qs_mn_ne _ (by rw [hk, ql_E_card hmu]; exact hj.symm))]; ring
    _ = ∑ k' : Fin N → Finset (Fin n), ∑ L' : Finset (Fin n), d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L' * ql_P (GLCoord ℤ n) k' L' i) := by
        refine sum_congr rfl fun k' _ => ql_sum_L (b := b) (fun L' => d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L' * ql_P (GLCoord ℤ n) k' L' i)) ?_
        intro L' hL'
        show d * (_ * qs_mn (qs_gC n) L.1 L' * _) = 0
        rw [qs_mn_ne _ (by rw [L.2]; exact hL'.symm)]; ring
    _ = ∑ i' : Fin N → Finset (Fin n), d * (ql_P (GLCoord ℤ n) k L.1 i' * ∏ j, qs_mn (qs_gC n) (i' j) (i j)) := by
        rw [← mul_sum, ← ql_P_equiv]; simp only [mul_sum]
    _ = ∑ I' : TIdx nu, d * (ql_P (GLCoord ℤ n) k L.1 (ql_E lo N (qs_ext nu I')) *
          ∏ j, qs_mn (qs_gC n) (ql_E lo N (qs_ext nu I') j) (i j)) := by
        symm
        refine sum_indices_eq_sum_columns hnu n1 n2 (fun i' => d * (ql_P (GLCoord ℤ n) k L.1 i' *
          ∏ j, qs_mn (qs_gC n) (i' j) (i j))) ?_
        rintro f ⟨j, hj⟩
        show d * (_ * ∏ j, qs_mn (qs_gC n) (f j) (i j)) = 0
        rw [prod_eq_zero (mem_univ j) (qs_mn_ne _ (by rw [hi, ql_E_card hnu]; exact hj))]; ring
    _ = ∑ I' : TIdx nu, ((ql_P ℤ k L.1 (ql_E lo N (qs_ext nu I')) : ℤ) : GLCoord ℤ n) * TMat nu I' I := by
        refine sum_congr rfl fun I' _ => ?_
        rw [ql_TMat hnu n1 n2, ql_P_cast]; ring
end Formalism.InvariantFactorPaths.ColumnFamilies
