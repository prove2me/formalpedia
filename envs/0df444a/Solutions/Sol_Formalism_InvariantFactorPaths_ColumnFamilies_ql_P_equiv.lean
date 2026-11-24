-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_P_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:15:01.356671+00:00
-- url     : https://prove2.me/submissions/7bcb96db-ba1c-4375-990e-10c9d9b13cb7

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_prod_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_W_equiv
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_lapT


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
theorem _root_.solution {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n)) (i : Fin N → Finset (Fin n)) :
    ∑ k' : Fin N → Finset (Fin n), ∑ L', (∏ j, qs_mn g (k j) (k' j)) * qs_mn g L L' * ql_P R k' L' i =
      ∑ i' : Fin N → Finset (Fin n), ql_P R k L i' * ∏ j, qs_mn g (i' j) (i j) := by
  calc ∑ k' : Fin N → Finset (Fin n), ∑ L', (∏ j, qs_mn g (k j) (k' j)) * qs_mn g L L' * ql_P R k' L' i
      = ∑ k' : Fin N → Finset (Fin n), ∑ D : Fin N → Finset (Fin n),
          (∏ j, qs_mn g (k j) (k' j)) * (∏ j, ql_w R (k' j) (D j) (i j)) * ∑ L', qs_mn g L L' * wedgeCoeff R D L' := by
        refine sum_congr rfl fun k' _ => ?_
        simp only [ql_P, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun D _ => sum_congr rfl fun L' _ => by ring
    _ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L * ∑ k' : Fin N → Finset (Fin n), ∑ D : Fin N → Finset (Fin n),
          ∏ j, qs_mn g (k j) (k' j) * qs_mn g (D' j) (D j) * ql_w R (k' j) (D j) (i j) := by
        simp only [← ql_W_equiv, mul_sum, prod_mul_distrib]
        symm
        rw [sum_comm]; refine sum_congr rfl fun k' _ => ?_
        rw [sum_comm]; exact sum_congr rfl fun D _ => sum_congr rfl fun D' _ => by ring
    _ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L *
          ∏ j, ∑ a, ∑ d, qs_mn g (k j) a * qs_mn g (D' j) d * ql_w R a d (i j) := by
        refine sum_congr rfl fun D' _ => ?_
        rw [ql_prod_sum (fun j a => ∑ d, qs_mn g (k j) a * qs_mn g (D' j) d * ql_w R a d (i j))]
        refine congrArg _ (sum_congr rfl fun k' _ => ?_)
        exact (ql_prod_sum (fun j d => qs_mn g (k j) (k' j) * qs_mn g (D' j) d * ql_w R (k' j) d (i j))).symm
    _ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L *
          ∑ i' : Fin N → Finset (Fin n), ∏ j, ql_w R (k j) (D' j) (i' j) * qs_mn g (i' j) (i j) := by
        simp only [ql_lapT, ql_prod_sum]
    _ = ∑ i' : Fin N → Finset (Fin n), ql_P R k L i' * ∏ j, qs_mn g (i' j) (i j) := by
        simp only [ql_P, mul_sum, sum_mul, prod_mul_distrib]
        rw [sum_comm]
        exact sum_congr rfl fun D _ => sum_congr rfl fun L' _ => by ring
end Formalism.InvariantFactorPaths.ColumnFamilies
