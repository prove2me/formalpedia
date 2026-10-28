-- Prove2me | solution 1 for D1Bound5.bennettPolynomialMatrix_det_monomial
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:48.448955+00:00
-- url     : https://prove2.me/submissions/02ad4ff6-09f2-4c53-b524-298fde483652

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettResidualCancellation_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_dvd
import Theorems.Thm_D1Bound5_bennettResidueTaylor_natDegree_le
import Theorems.Thm_D1Bound5_polynomial_det_eq_monomial_of_residual

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]









section Nodes

variable {I : Type*} [DecidableEq I]



theorem bennettPolynomialResidue_natDegree_le (s : Finset I) (a : I → F)
    (k : ℕ) (ν : F) (i j : I) :
    (bennettPolynomialResidue s a k ν i j).natDegree ≤ k := by
  apply bennettResidueTaylor_natDegree_le
  split_ifs <;> omega



end Nodes

end D1Bound5
end

section
open Finset Polynomial Matrix

namespace D1Bound5

/-!
This module isolates an intermediate step in the all-orders Bennett determinant
argument. It does not define the residue polynomials or prove their cancellation.
The required cancellation is an explicit hypothesis of the final theorem.
-/

section CommRing

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]









/-- Uniform-degree form of the preceding intermediate principle. This gives the
`card(ι) * k` exponent appearing in the all-orders Bennett determinant. -/
theorem polynomial_det_eq_monomial_of_uniform_residual (P : Matrix ι ι R[X])
    (k : ℕ) (θ : ι → R[X]) (q : ι) (hθ : θ q = 1)
    (hdeg : ∀ i j, (P i j).natDegree ≤ k)
    (hres : ∀ i, (X : R[X]) ^ (Fintype.card ι * k) ∣ ∑ j, θ j * P i j) :
    P.det = C (P.det.coeff (Fintype.card ι * k)) * X ^ (Fintype.card ι * k) := by
  simpa using polynomial_det_eq_monomial_of_residual P (fun _ ↦ k) θ q hθ hdeg
    (by simpa using hres)

end CommRing

end D1Bound5
end

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]









/-- The determinant of the actual arbitrary-order Bennett matrix is a single
monomial. This proves its exact possible degree without assuming residual
cancellation; the value and nonvanishing of its coefficient are separate. -/
theorem _root_.solution
    (a : I → F) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν : F) (q : I) (hq : a q = 0) :
    (bennettPolynomialMatrix a k ν).det =
      Polynomial.C ((bennettPolynomialMatrix a k ν).det.coeff (Fintype.card I * k)) *
        Polynomial.X ^ (Fintype.card I * k) := by
  apply polynomial_det_eq_monomial_of_uniform_residual
    (θ := fun j ↦ PowerSeries.trunc (Fintype.card I * k)
      (PowerSeries.rescale (a j) (PowerSeries.binomialSeries F ν))) (q := q)
  · have hD : 0 < Fintype.card I * k :=
      Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨q⟩) hk
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
    rw [hq, PowerSeries.rescale_zero_apply, PowerSeries.binomialSeries_constantCoeff,
      map_one, hd]
    exact PowerSeries.trunc_one d
  · intro i j
    exact bennettPolynomialResidue_natDegree_le Finset.univ a k ν i j
  · intro i
    exact bennettPolynomialResidue_residual_dvd a ha k hk ν i

end Nodes

end D1Bound5
end
