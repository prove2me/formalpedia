-- Prove2me | solution 1 for D1Bound5.bennettLocalResidue_sum_X_pow_eq_infinity_coeff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:36:31.232071+00:00
-- url     : https://prove2.me/submissions/5dff2d3f-71e8-4e91-ab43-d475fa8f035d

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettPartialFractions_Definitions
import Definitions.Def_D1Bound5_BennettResiduesAtInfinity_Definitions
import Theorems.Thm_D1Bound5_bennettLocalResidue_sum_eq_remainder_coeff
import Theorems.Thm_D1Bound5_bennettPoleDenominator_monic
import Theorems.Thm_D1Bound5_bennettPoleDenominator_natDegree
import Theorems.Thm_D1Bound5_bennettReciprocalInfinity_mul
import Theorems.Thm_D1Bound5_bennett_inverse_reverse_coeff

section
open Finset Polynomial

namespace D1Bound5

section Reverse

variable {F : Type*} [Field F]



end Reverse

section Residues

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]















/-- Exact all-orders residue identity above the cancellation threshold.
The low-degree zero-residue theorem and this formula together determine
every coefficient of the actual Bennett row residual. -/
theorem _root_.solution
    (a : ι → F) (ha : Function.Injective a) (e : ι → ℕ)
    (hd : 0 < ∑ i, (e i + 1)) (t : ℕ) :
    ∑ i, bennettLocalResidue a e (X ^ ((∑ l, (e l + 1)) - 1 + t)) i =
      PowerSeries.coeff t (bennettReciprocalInfinity a e) := by
  rw [bennettLocalResidue_sum_eq_remainder_coeff a ha e]
  have h := bennett_inverse_reverse_coeff
    (bennettPoleDenominator a e) (bennettPoleDenominator_monic a e)
    (by simpa only [bennettPoleDenominator_natDegree] using hd)
    (bennettReciprocalInfinity a e) (bennettReciprocalInfinity_mul a e) t
  simpa only [bennettPoleDenominator_natDegree] using h.symm

end Residues

end D1Bound5
end
