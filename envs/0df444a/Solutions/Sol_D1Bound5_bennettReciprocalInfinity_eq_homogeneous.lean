-- Prove2me | solution 1 for D1Bound5.bennettReciprocalInfinity_eq_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:36:35.996133+00:00
-- url     : https://prove2.me/submissions/9caa3ea0-11d3-4501-a406-74d35cbe9887

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
import Definitions.Def_D1Bound5_BennettResiduesAtInfinity_Definitions
import Theorems.Thm_D1Bound5_bennettHomogeneousSeries_mul
import Theorems.Thm_D1Bound5_bennettNegativeBinomial_mul

section
open Finset

namespace D1Bound5

section Homogeneous

variable {R ι : Type*} [CommRing R] [DecidableEq ι]









end Homogeneous

section Repeated

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]





private theorem bennettReciprocalInfinity_explicit_mul
    (a : ι → F) (e : ι → ℕ) :
    (∏ i, (1 - PowerSeries.C (a i) * PowerSeries.X) ^ (e i + 1)) *
      bennettReciprocalInfinity a e = 1 := by
  unfold bennettReciprocalInfinity
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i hi
  have h := congrArg (PowerSeries.rescale (-a i))
    (bennettNegativeBinomial_mul (F := F) (e i + 1))
  simpa only [map_mul, map_pow, map_add, map_one, PowerSeries.rescale_X,
    map_neg, neg_mul, sub_eq_add_neg] using h

/-- The reciprocal pole product is exactly the generating series of complete
homogeneous polynomials on the repeated nodes. Distinctness is unnecessary. -/
theorem _root_.solution
    (a : ι → F) (e : ι → ℕ) :
    bennettReciprocalInfinity a e =
      bennettHomogeneousSeries (fun i : BennettRepeatedNodes e => a i.1) := by
  classical
  let D : PowerSeries F :=
    ∏ i, (1 - PowerSeries.C (a i) * PowerSeries.X) ^ (e i + 1)
  have hden : (∏ i : BennettRepeatedNodes e,
      (1 - PowerSeries.C (a i.1) * PowerSeries.X)) = D := by
    rw [Fintype.prod_sigma]
    simp [D]
  have hhom : D * bennettHomogeneousSeries (fun i : BennettRepeatedNodes e => a i.1) = 1 := by
    rw [← hden]
    exact bennettHomogeneousSeries_mul _
  have hinf : D * bennettReciprocalInfinity a e = 1 :=
    bennettReciprocalInfinity_explicit_mul a e
  calc
    bennettReciprocalInfinity a e = bennettReciprocalInfinity a e * 1 := by ring
    _ = bennettReciprocalInfinity a e *
        (D * bennettHomogeneousSeries (fun i : BennettRepeatedNodes e => a i.1)) := by
          rw [hhom]
    _ = (D * bennettReciprocalInfinity a e) *
        bennettHomogeneousSeries (fun i : BennettRepeatedNodes e => a i.1) := by ring
    _ = _ := by rw [hinf, one_mul]





end Repeated

end D1Bound5
end
