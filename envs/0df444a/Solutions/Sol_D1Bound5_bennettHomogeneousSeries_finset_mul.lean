-- Prove2me | solution 1 for D1Bound5.bennettHomogeneousSeries_finset_mul
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:57.491997+00:00
-- url     : https://prove2.me/submissions/dcfb12e0-65cf-45f5-a3f4-d427e73cf374

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettRepeatedHsymm_Definitions
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions
import Theorems.Thm_D1Bound5_homogeneousMultisetSum_insert
import Theorems.Thm_D1Bound5_homogeneousMultisetSum_zero

section
open Finset

namespace D1Bound5

section Homogeneous

variable {R ι : Type*} [CommRing R] [DecidableEq ι]



private theorem bennettHomogeneousSeries_insert
    (s : Finset ι) (a : ι → R) (i : ι) (hi : i ∉ s) :
    (1 - PowerSeries.C (a i) * PowerSeries.X) *
      bennettHomogeneousSeries (fun j : (insert i s : Finset ι) => a j) =
      bennettHomogeneousSeries (fun j : s => a j) := by
  ext n
  rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul]
  cases n with
  | zero =>
      have hzero (G : PowerSeries R) : PowerSeries.coeff 0 (PowerSeries.X * G) = 0 := by
        simpa using PowerSeries.coeff_X_pow_mul' G 1 0
      rw [hzero]
      simp [bennettHomogeneousSeries]
  | succ n =>
      have hsucc (G : PowerSeries R) : PowerSeries.coeff (n + 1) (PowerSeries.X * G) =
          PowerSeries.coeff n G := by
        simpa only [pow_one] using PowerSeries.coeff_X_pow_mul G 1 n
      rw [hsucc]
      simp only [bennettHomogeneousSeries, PowerSeries.coeff_mk]
      rw [homogeneousMultisetSum_insert s a i hi n]
      ring

/-- The exact generating identity for complete homogeneous polynomials over
a finite set, proved by the already established variable-adjunction recursion. -/
theorem _root_.solution
    (s : Finset ι) (a : ι → R) :
    (∏ i ∈ s, (1 - PowerSeries.C (a i) * PowerSeries.X)) *
      bennettHomogeneousSeries (fun i : s => a i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, one_mul]
      ext n
      cases n with
      | zero => simp [bennettHomogeneousSeries]
      | succ n => simp [bennettHomogeneousSeries, homogeneousMultisetSum]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      calc
        _ = (∏ j ∈ s, (1 - PowerSeries.C (a j) * PowerSeries.X)) *
            ((1 - PowerSeries.C (a i) * PowerSeries.X) *
              bennettHomogeneousSeries (fun j : (insert i s : Finset ι) => a j)) := by ring
        _ = _ := by rw [bennettHomogeneousSeries_insert s a i hi, ih]



end Homogeneous

section Repeated

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]













end Repeated

end D1Bound5
end
