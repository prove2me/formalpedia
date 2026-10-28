-- Prove2me | solution 1 for D1Bound5.bennettLocalResidue_sum_X_pow_eq_hsymm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:33:59.474388+00:00
-- url     : https://prove2.me/submissions/9b903275-3eb0-4ae3-a591-54dedff95b1b

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
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettRepeatedHsymm_Definitions
import Definitions.Def_D1Bound5_BennettResiduesAtInfinity_Definitions
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions
import Theorems.Thm_D1Bound5_bennettLocalResidue_sum_X_pow_eq_infinity_coeff
import Theorems.Thm_D1Bound5_bennettReciprocalInfinity_eq_homogeneous
import Theorems.Thm_D1Bound5_homogeneousMultisetSum_eq_hsymm

section
open Finset

namespace D1Bound5

section Homogeneous

variable {R ι : Type*} [CommRing R] [DecidableEq ι]









end Homogeneous

section Repeated

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]









theorem bennettReciprocalInfinity_coeff_eq_hsymm
    (a : ι → F) (e : ι → ℕ) (t : ℕ) :
    PowerSeries.coeff t (bennettReciprocalInfinity a e) =
      MvPolynomial.aeval (fun i : BennettRepeatedNodes e => a i.1)
        (MvPolynomial.hsymm (BennettRepeatedNodes e) F t) := by
  rw [bennettReciprocalInfinity_eq_homogeneous]
  simp only [bennettHomogeneousSeries, PowerSeries.coeff_mk]
  exact homogeneousMultisetSum_eq_hsymm _ t

/-- The actual high-degree residue sum is a complete homogeneous polynomial
on repeated nodes, supplying the exact input to the Bennett tail majorant. -/
theorem _root_.solution
    (a : ι → F) (ha : Function.Injective a) (e : ι → ℕ)
    (hd : 0 < ∑ i, (e i + 1)) (t : ℕ) :
    ∑ i, bennettLocalResidue a e
        (Polynomial.X ^ ((∑ l, (e l + 1)) - 1 + t)) i =
      MvPolynomial.aeval (fun i : BennettRepeatedNodes e => a i.1)
        (MvPolynomial.hsymm (BennettRepeatedNodes e) F t) := by
  rw [bennettLocalResidue_sum_X_pow_eq_infinity_coeff a ha e hd t,
    bennettReciprocalInfinity_coeff_eq_hsymm]

end Repeated

end D1Bound5
end
