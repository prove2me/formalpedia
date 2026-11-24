-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_W_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:11:38.702965+00:00
-- url     : https://prove2.me/submissions/61655167-678e-4721-b1ad-68c5a5e11ae4

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_W_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sum_cons
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_lapM
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_mn_empty


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
variable {R : Type*} [CommRing R]
variable (g : Matrix (Fin n) (Fin n) R)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)) (L : Finset (Fin n)),
    ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g (D' j) (D j)) * wedgeCoeff R D' L = ∑ L', qs_mn g L L' * wedgeCoeff R D L'
  | 0, D, L => by
    simp [wedgeCoeff, ql_U, ql_sW, ql_mn_empty, eq_comm]
  | N + 1, D, L => by
    rw [ql_sum_cons]
    calc ∑ a, ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g ((Fin.cons a D' : Fin (N + 1) → _) j) (D j)) *
            wedgeCoeff R (Fin.cons a D' : Fin (N + 1) → _) L
        = ∑ a, ∑ M, qs_mn g a (D 0) * ql_w R a M L *
            ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g (D' j) (Fin.tail D j)) * wedgeCoeff R D' M := by
          refine sum_congr rfl fun a _ => ?_
          simp only [ql_W_succ (Fin.cons a _), Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail_cons,
            mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun M _ => sum_congr rfl fun D' _ => by simp only [Fin.tail]; ring
      _ = ∑ a, ∑ M, qs_mn g a (D 0) * ql_w R a M L * ∑ M', qs_mn g M M' * wedgeCoeff R (Fin.tail D) M' := by
          simp only [solution N]
      _ = ∑ M', wedgeCoeff R (Fin.tail D) M' * ∑ a, ∑ M, qs_mn g a (D 0) * qs_mn g M M' * ql_w R a M L := by
          simp only [mul_sum]
          symm
          rw [sum_comm]; refine sum_congr rfl fun a _ => ?_
          rw [sum_comm]; exact sum_congr rfl fun M _ => sum_congr rfl fun M' _ => by ring
      _ = ∑ L', qs_mn g L L' * wedgeCoeff R D L' := by
          simp only [ql_lapM, ql_W_succ D, mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun M _ => sum_congr rfl fun D' _ => by ring
end Formalism.InvariantFactorPaths.ColumnFamilies
