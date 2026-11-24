-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_prod_conv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:24.281752+00:00
-- url     : https://prove2.me/submissions/4e050b27-53cd-4369-8cdd-6633831e6deb

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntLam

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∏ j ∈ range n, ∏ i ∈ range j, F i j = ∏ i : Fin n, ∏ j ∈ Ioi i, F i j := by
  have h1 : ∀ i : Fin n, ∏ j ∈ Ioi i, F i j = ∏ j : Fin n, if i < j then F i j else 1 := by
    intro i
    rw [← prod_filter]
    congr 1
    ext j
    simp
  simp_rw [h1]
  rw [prod_comm, ← Fin.prod_univ_eq_prod_range (fun j => ∏ i ∈ range j, F i j) n]
  refine prod_congr rfl fun j _ => ?_
  have h2 : ∏ i : Fin n, (if i < j then F i j else 1) = ∏ i ∈ range n, if i < j.1 then F i j else 1 := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => if i < j.1 then F i j else 1) n]
    refine prod_congr rfl fun i _ => ?_
    simp only [Fin.lt_def]
  rw [h2, ← prod_filter]
  congr 1
  ext i
  have := j.2
  simp only [mem_range, mem_filter]
  omega
end Formalism.InvariantFactorPaths.ColumnFamilies
