-- Prove2me | solution 1 for D1Bound5.bennettClearedMatrix_det_eval_zero_formula
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:53.001722+00:00
-- url     : https://prove2.me/submissions/4a9f4234-403a-4250-9dd2-ce9b791c68c3

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions
import Definitions.Def_D1Bound5_BennettDeterminantFormula_Definitions
import Definitions.Def_D1Bound5_BennettResidualCancellation_Definitions
import Theorems.Thm_D1Bound5_bennettBinomialProduct_succ
import Theorems.Thm_D1Bound5_bennettClearedMatrix_det_constant
import Theorems.Thm_D1Bound5_bennettClearedMatrix_det_remove_last
import Theorems.Thm_D1Bound5_bennettClearedResidue_diagonal_at_node
import Theorems.Thm_D1Bound5_bennettDirectedProduct_succ

section
open Finset

namespace D1Bound5

variable {F I : Type*} [Field F] [CharZero F]
variable [Fintype I] [DecidableEq I]









/-- Any two evaluations of the cleared determinant agree. -/
theorem bennettClearedMatrix_det_eval_eq
    (a : I → F) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν : F) (q : I) (hq : a q = 0) (N M : F) :
    (bennettClearedMatrix a k ν).det.eval N =
      (bennettClearedMatrix a k ν).det.eval M := by
  simp only [bennettClearedMatrix_det_constant a ha k hk ν q hq, Polynomial.eval_C]

end D1Bound5
end

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]









/-- Exact all-order determinant evaluation. In the induction the final node
is removed, retaining the distinguished zero node in every nonempty prefix. -/
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) :
    ∀ (n : ℕ) (a : Fin (n + 1) → F), Function.Injective a →
      ∀ (ν : F), a 0 = 0 →
        (bennettClearedMatrix a k ν).det.eval 0 =
          bennettBinomialProduct (n + 1) k ν * bennettDirectedProduct a k := by
  intro n
  induction n with
  | zero =>
      intro a ha ν h0
      rw [Matrix.det_fin_one]
      change (bennettClearedResidue Finset.univ a k ν 0 0).eval 0 = _
      have hdiag := bennettClearedResidue_diagonal_at_node Finset.univ a k ν (0 : Fin 1)
      rw [h0, neg_zero] at hdiag
      rw [hdiag]
      simp [bennettBinomialProduct, bennettDirectedProduct]
  | succ n ih =>
      intro a ha ν h0
      let b : Fin (n + 1) → F := fun j ↦ a j.castSucc
      have hb : Function.Injective b := ha.comp (Fin.castSucc_injective (n + 1))
      have hb0 : b 0 = 0 := h0
      calc
        _ = (bennettClearedMatrix a k ν).det.eval (-a (Fin.last (n + 1))) :=
          bennettClearedMatrix_det_eval_eq a ha k hk ν 0 h0 0 _
        _ = Ring.choose ((k : F) + ν) k *
            (∏ j : Fin (n + 1), ((a (Fin.last (n + 1)) - a j.castSucc)⁻¹) ^ k) *
            (∏ j : Fin (n + 1), ((a j.castSucc - a (Fin.last (n + 1)))⁻¹) ^ k) *
            (bennettClearedMatrix b k (ν - (k : F))).det.eval
              (-a (Fin.last (n + 1))) :=
          bennettClearedMatrix_det_remove_last (n + 1) a ha k hk ν
        _ = Ring.choose ((k : F) + ν) k *
            (∏ j : Fin (n + 1), ((a (Fin.last (n + 1)) - a j.castSucc)⁻¹) ^ k) *
            (∏ j : Fin (n + 1), ((a j.castSucc - a (Fin.last (n + 1)))⁻¹) ^ k) *
            (bennettBinomialProduct (n + 1) k (ν - (k : F)) *
              bennettDirectedProduct b k) := by
          rw [bennettClearedMatrix_det_eval_eq b hb k hk (ν - (k : F)) 0 hb0
            (-a (Fin.last (n + 1))) 0, ih b hb (ν - (k : F)) hb0]
        _ = _ := by
          rw [bennettBinomialProduct_succ (n + 1) k ν,
            bennettDirectedProduct_succ (n + 1) a k]
          dsimp [b]
          ring





end D1Bound5
end
