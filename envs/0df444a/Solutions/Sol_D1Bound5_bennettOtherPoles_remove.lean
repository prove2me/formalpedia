-- Prove2me | solution 1 for D1Bound5.bennettOtherPoles_remove
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:13.31824+00:00
-- url     : https://prove2.me/submissions/07f95ebf-dfb4-4e72-89b7-94237474a08b

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]









section Nodes

variable {I : Type*} [DecidableEq I]







/-- Removing a different node splits off exactly its reciprocal pole. -/
theorem _root_.solution (s : Finset I) (a : I → F)
    (k : ℕ) (i j q : I) (hq : q ∈ s) (hiq : i ≠ q) (hjq : j ≠ q) :
    bennettOtherPoles s a k i j =
      bennettPoleSeries (a j - a q) k *
        bennettOtherPoles (s.erase q) a k i j := by
  have hqj : q ∈ s.erase j := Finset.mem_erase.mpr ⟨hjq.symm, hq⟩
  unfold bennettOtherPoles
  rw [← Finset.mul_prod_erase (s.erase j)
    (fun l => bennettPoleSeries (a j - a l) (k + if i = l then 1 else 0)) hqj]
  simp only [if_neg hiq, add_zero, Finset.erase_right_comm]









end Nodes

end D1Bound5
end
