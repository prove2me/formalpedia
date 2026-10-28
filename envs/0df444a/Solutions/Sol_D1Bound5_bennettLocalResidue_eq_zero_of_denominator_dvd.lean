-- Prove2me | solution 1 for D1Bound5.bennettLocalResidue_eq_zero_of_denominator_dvd
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:35.833786+00:00
-- url     : https://prove2.me/submissions/7791c77a-b073-4712-9830-23e5c9e6fe37

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettPartialFractions_Definitions
import Theorems.Thm_D1Bound5_bennettShiftToSeries_linear

section
open Finset Polynomial

namespace D1Bound5

section Reverse

variable {F : Type*} [Field F]



end Reverse

section Residues

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]

/-- A numerator divisible by the full denominator has zero local residue.
This includes the polynomial part of an improper partial fraction. -/
theorem _root_.solution
    (a : ι → F) (e : ι → ℕ) (f : F[X])
    (hf : bennettPoleDenominator a e ∣ f) (i : ι) :
    bennettLocalResidue a e f i = 0 := by
  have hdiv : (X - C (a i)) ^ (e i + 1) ∣ f := by
    apply dvd_trans _ hf
    exact Finset.dvd_prod_of_mem
      (fun l : ι => (X - C (a l)) ^ (e l + 1)) (Finset.mem_univ i)
  have hshift : (PowerSeries.X : PowerSeries F) ^ (e i + 1) ∣
      bennettShiftToSeries (a i) f := by
    simpa only [map_pow, bennettShiftToSeries_linear, sub_self, map_zero, zero_add]
      using map_dvd (bennettShiftToSeries (a i)) hdiv
  exact PowerSeries.X_pow_dvd_iff.mp
    (dvd_mul_of_dvd_left hshift (bennettLocalReciprocal a e i))
    (e i) (Nat.lt_succ_self _)















end Residues

end D1Bound5
end
