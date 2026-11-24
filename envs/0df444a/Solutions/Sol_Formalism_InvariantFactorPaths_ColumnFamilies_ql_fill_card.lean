-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_fill_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:54.301833+00:00
-- url     : https://prove2.me/submissions/8983441f-332e-4ee6-b4fa-28b56bcb04e1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_high
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_low


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
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ} (h1 : lo ≤ mu (lastIdx n))
    (h2 : mu 0 ≤ lo + N) (f : Fin N → Finset (Fin n)) (hf : ∀ j : Fin N, (f j).card = colH mu (lo + 1 + (j : ℕ))) (c : ℤ) :
    (ql_fill lo N f c).card = colH mu c := by
  unfold ql_fill
  split_ifs with h h'
  · rw [hf]; congr 1
    show lo + 1 + ((c - lo - 1).toNat : ℤ) = c
    omega
  · rw [qs_colH_low hmu (h'.trans h1)]; simp
  · rw [qs_colH_high hmu (by omega)]; simp
end Formalism.InvariantFactorPaths.ColumnFamilies
