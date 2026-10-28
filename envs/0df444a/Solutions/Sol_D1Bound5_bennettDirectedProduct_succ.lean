-- Prove2me | solution 1 for D1Bound5.bennettDirectedProduct_succ
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:11:54.435+00:00
-- url     : https://prove2.me/submissions/4067aedc-23d6-43b7-adcb-1f364732b97e

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
import Definitions.Def_D1Bound5_BennettDeterminantFormula_Definitions
import Theorems.Thm_D1Bound5_bennett_prod_erase_last
import Theorems.Thm_D1Bound5_bennett_prod_erase_last_erase

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]







/-- Splitting the ordered-pair product exposes the two directions involving
the removed node and leaves the ordered-pair product on the prefix. -/
theorem _root_.solution (n : ℕ) (a : Fin (n + 1) → F) (k : ℕ) :
    bennettDirectedProduct a k =
      (∏ j : Fin n, ((a (Fin.last n) - a j.castSucc)⁻¹) ^ k) *
        (∏ j : Fin n, ((a j.castSucc - a (Fin.last n))⁻¹) ^ k) *
          bennettDirectedProduct (fun j : Fin n ↦ a j.castSucc) k := by
  have hinner (i : Fin n) :
      (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i.castSucc,
        ((a i.castSucc - a j)⁻¹) ^ k) =
        ((a i.castSucc - a (Fin.last n))⁻¹) ^ k *
          ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
            ((a i.castSucc - a j.castSucc)⁻¹) ^ k := by
    have hmem : Fin.last n ∈ (Finset.univ : Finset (Fin (n + 1))).erase i.castSucc := by
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      have hv := congrArg (fun j : Fin (n + 1) => j.val) h
      change n = i.val at hv
      have hi := i.isLt
      omega
    rw [← Finset.mul_prod_erase (Finset.univ.erase i.castSucc)
      (fun j ↦ ((a i.castSucc - a j)⁻¹) ^ k) hmem]
    rw [Finset.erase_right_comm, bennett_prod_erase_last_erase]
  unfold bennettDirectedProduct
  rw [Fin.prod_univ_castSucc, bennett_prod_erase_last]
  simp_rw [hinner]
  rw [Finset.prod_mul_distrib]
  ring







end D1Bound5
end
