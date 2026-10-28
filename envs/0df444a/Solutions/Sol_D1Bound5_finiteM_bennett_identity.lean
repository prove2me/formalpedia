-- Prove2me | solution 1 for D1Bound5.finiteM_bennett_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:23:59.735195+00:00
-- url     : https://prove2.me/submissions/9000fa94-6b57-4589-8279-1f8b3e4bc31f

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Definitions.Def_D1Bound5_FiniteMBennettIdentity_Definitions
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions
import Theorems.Thm_D1Bound5_bennettPoleSeries_coeff

section
open Finset Polynomial

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]





private theorem finiteM_prod_erase_four {M : Type*} [CommMonoid M]
    (g : Fin 4 → M) (j : Fin 4) :
    (∏ l ∈ (Finset.univ : Finset (Fin 4)).erase j, g l) =
      (if (0 : Fin 4) = j then 1 else g 0) *
      (if (1 : Fin 4) = j then 1 else g 1) *
      (if (2 : Fin 4) = j then 1 else g 2) *
      (if (3 : Fin 4) = j then 1 else g 3) := by
  classical
  calc
    _ = ∏ l ∈ (Finset.univ : Finset (Fin 4)).erase j,
        (if l = j then 1 else g l) := by
      apply Finset.prod_congr rfl
      intro l hl
      have hne : l ≠ j := (Finset.mem_erase.mp hl).1
      simp only [if_neg hne]
    _ = ∏ l : Fin 4, (if l = j then 1 else g l) :=
      Finset.prod_erase Finset.univ (by simp)
    _ = _ := Fin.prod_univ_four _

private theorem finiteM_pole_constantCoeff (d : F) (k : ℕ) :
    PowerSeries.constantCoeff (bennettPoleSeries d k) = (d⁻¹)^k := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff, Ring.choose_zero_right,
    one_mul, add_zero] using bennettPoleSeries_coeff d k 0

private theorem finiteM_choose_two (r : F) : Ring.choose r 2 = r*(r-1)/2 := by
  have h := Ring.choose_smul_choose (r := r) (n := 2) (k := 1) (by decide)
  norm_num [nsmul_eq_mul, Ring.choose_one_right] at h
  apply (eq_div_iff (by norm_num : (2 : F) ≠ 0)).mpr
  linear_combination h

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 4096 in
/-- Exact comparison with the actual arbitrary-order residue construction.
All row and root-column divisions are accounted for by integer polynomials;
no residue decomposition or formal identity is assumed. -/
theorem _root_.solution (a b s c : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) (i j : Fin 4) :
    finiteMBennettEntry a b s c i j =
      finiteMRowFactor a b s i * finiteMMatrix a b s c i j := by
  have hfi01 : (0 : Fin 4) ≠ 1 := by decide
  have hfi02 : (0 : Fin 4) ≠ 2 := by decide
  have hfi03 : (0 : Fin 4) ≠ 3 := by decide
  have hfi12 : (1 : Fin 4) ≠ 2 := by decide
  have hfi13 : (1 : Fin 4) ≠ 3 := by decide
  have hfi23 : (2 : Fin 4) ≠ 3 := by decide
  have hnode0 : finiteMNodes a b s 0 = 0 := rfl
  have hnode1 : finiteMNodes a b s 1 = b*s := rfl
  have hnode2 : finiteMNodes a b s 2 = a*s := rfl
  have hnode3 : finiteMNodes a b s 3 = a*b := rfl
  have hu4 : (univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  have hanti0 : Finset.antidiagonal 0 = {(0,0)} := by decide
  have hanti1 : Finset.antidiagonal 1 = {(0,1),(1,0)} := by decide
  have hanti2 : Finset.antidiagonal 2 = {(0,2),(1,1),(2,0)} := by decide
  have hs0 : (univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have hs1 : (univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have hs2 : (univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have hs3 : (univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  have hab0 : a-b ≠ 0 := sub_ne_zero.mpr hab
  have has0 : a-s ≠ 0 := sub_ne_zero.mpr has
  have hbs0 : b-s ≠ 0 := sub_ne_zero.mpr hbs
  have hba0 : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hsa0 : s-a ≠ 0 := sub_ne_zero.mpr has.symm
  have hsb0 : s-b ≠ 0 := sub_ne_zero.mpr hbs.symm
  have hcases : ∀ x : Fin 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases hcases i with rfl | rfl | rfl | rfl <;>
    rcases hcases j with rfl | rfl | rfl | rfl
  all_goals
    norm_num [finiteMBennettEntry, bennettClearedResidue,
      bennettClearedTaylor, bennettOtherPoles, finiteM_prod_erase_four,
      hnode0, hnode1, hnode2, hnode3,
      hfi01, hfi01.symm, hfi02, hfi02.symm, hfi03, hfi03.symm, hfi12, hfi12.symm, hfi13, hfi13.symm, hfi23, hfi23.symm,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      hanti1, hanti2, hanti0,
      PowerSeries.coeff_mul, bennettPoleSeries_coeff, finiteM_pole_constantCoeff,
      Ring.choose_zero_right, Ring.choose_one_right, finiteM_choose_two,
      finiteMRowFactor, finiteMMatrix, Matrix.mul_diagonal,
      finiteMDividedMatrix, finiteMTerms, finiteMTermEval]
  all_goals
    try simp only [show b*s-a*s = (b-a)*s by ring,
      show b*s-a*b = b*(s-a) by ring,
      show a*s-b*s = (a-b)*s by ring,
      show a*s-a*b = a*(s-b) by ring,
      show a*b-b*s = b*(a-s) by ring,
      show a*b-a*s = a*(b-s) by ring]
    field_simp [ha, hb, hs, hab0, has0, hbs0, hba0, hsa0, hsb0]
    <;> ring





end D1Bound5
end
