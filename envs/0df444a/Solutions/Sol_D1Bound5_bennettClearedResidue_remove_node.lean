-- Prove2me | solution 1 for D1Bound5.bennettClearedResidue_remove_node
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:49.392798+00:00
-- url     : https://prove2.me/submissions/23ea5b49-facb-460f-ba01-fd0602b5dbca

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Theorems.Thm_D1Bound5_bennettClearedTaylor_eval_remove_pole
import Theorems.Thm_D1Bound5_bennettOtherPoles_remove

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]









section Nodes

variable {I : Type*} [DecidableEq I]









/-- Exact arbitrary-order node removal, including the parameter shift ν-k
and the full column scaling. No determinant formula is assumed. -/
theorem _root_.solution (s : Finset I) (a : I → F)
    (k : ℕ) (ν : F) (i j q : I) (hq : q ∈ s)
    (hiq : i ≠ q) (hjq : j ≠ q) (ha : a j ≠ a q) :
    (bennettClearedResidue s a k ν i j).eval (-a q) =
      ((a j - a q)⁻¹) ^ k *
        (bennettClearedResidue (s.erase q) a k (ν - (k : F)) i j).eval (-a q) := by
  have hr : k + (if i = j then 1 else 0) - 1 ≤ k := by split_ifs <;> omega
  have hd : -a q + a j ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr ha
  unfold bennettClearedResidue
  rw [bennettOtherPoles_remove s a k i j q hq hiq hjq]
  have he : a j - a q = -a q + a j := by ring
  rw [he]
  exact bennettClearedTaylor_eval_remove_pole k _ hr ν (a j) (-a q) _ hd







end Nodes

end D1Bound5
end
