-- Prove2me | solution 1 for D1Bound5.bennettClearedResidue_diagonal_at_node
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:56.361566+00:00
-- url     : https://prove2.me/submissions/59007702-02f7-4200-97e1-f3949a5fa5be

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Theorems.Thm_D1Bound5_bennettPoleSeries_coeff

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]









section Nodes

variable {I : Type*} [DecidableEq I]













theorem bennettPoleSeries_constantCoeff (d : F) (k : ℕ) :
    PowerSeries.constantCoeff (bennettPoleSeries d k) = (d⁻¹) ^ k := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, bennettPoleSeries_coeff]
  simp

/-- The surviving diagonal entry at the removed node, with its exact
generalized binomial coefficient and every directed node difference. -/
theorem _root_.solution
    (s : Finset I) (a : I → F) (k : ℕ) (ν : F) (i : I) :
    (bennettClearedResidue s a k ν i i).eval (-a i) =
      Ring.choose ((k : F) + ν) k *
        ∏ l ∈ s.erase i, ((a i - a l)⁻¹) ^ k := by
  simp only [bennettClearedResidue, if_pos rfl, ite_true, Nat.add_sub_cancel,
    bennettClearedTaylor, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single (k, 0)]
  · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, neg_add_cancel, tsub_self,
      pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      bennettOtherPoles, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro l hl
    have hli : i ≠ l := (Finset.mem_erase.mp hl).1.symm
    simp only [if_neg hli, add_zero, bennettPoleSeries_constantCoeff]
  · intro ht hht hne
    have hsum := Finset.mem_antidiagonal.mp hht
    have hfirst : ht.1 ≠ k := by
      intro heq
      apply hne
      apply Prod.ext
      · exact heq
      · omega
    have hp : 0 < k - ht.1 := by omega
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, neg_add_cancel,
      zero_pow (Nat.ne_of_gt hp), mul_zero]
  · intro hn
    exact (hn (Finset.mem_antidiagonal.mpr (by omega))).elim

end Nodes

end D1Bound5
end
