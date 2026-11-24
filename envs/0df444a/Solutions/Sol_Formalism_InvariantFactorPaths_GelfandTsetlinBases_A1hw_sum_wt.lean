-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.sum_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:44.844376+00:00
-- url     : https://prove2.me/submissions/97c19c18-3fb7-42f3-8fe0-3e40cf2039a9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
theorem _root_.solution (x : ℤ) (S : Finset ℤ) (hS : Finset.Ioc 0 x ∪ Finset.Ioc x 0 ⊆ S) :
    ∑ c ∈ S, (if 1 ≤ c then (if c ≤ x then (1 : ℤ) else 0) else (if x < c then -1 else 0)) = x := by
  rw [← Finset.sum_subset hS]
  · rcases le_total 0 x with h | h
    · rw [Finset.Ioc_eq_empty (not_lt.2 h), Finset.union_empty]
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ))]
      · simp [h]
      · intro c hc
        rw [Finset.mem_Ioc] at hc
        rw [if_pos (by omega), if_pos hc.2]
    · rw [Finset.Ioc_eq_empty (not_lt.2 h), Finset.empty_union]
      rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℤ))]
      · simp [h]
      · intro c hc
        rw [Finset.mem_Ioc] at hc
        rw [if_neg (by omega), if_pos hc.1]
  · intro c _ hc
    rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ioc] at hc
    split_ifs <;> first | rfl | (exfalso; omega)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
