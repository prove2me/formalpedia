-- Prove2me | solution 1 for D1Bound5.bennettLocalResidue_clearedPole_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:35:05.641656+00:00
-- url     : https://prove2.me/submissions/e71d7345-6372-4213-9ad2-6d7bd892a1f1

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions
import Theorems.Thm_D1Bound5_bennettShiftToSeries_linear

section
open Finset

namespace D1Bound5

section Field

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]















/-- At another node, the cleared numerator contains the full local pole
factor, so its relevant residue coefficient vanishes. -/
theorem _root_.solution (a : ι → F) (e : ι → ℕ)
    (i l : ι) (hil : i ≠ l) (j : Fin (e l + 1)) :
    bennettLocalResidue a e (clearedPoleNumerator a e l j) i = 0 := by
  have hmem : i ∈ (Finset.univ : Finset ι).erase l :=
    Finset.mem_erase.mpr ⟨hil, Finset.mem_univ i⟩
  have hdiv : (Polynomial.X - Polynomial.C (a i)) ^ (e i + 1) ∣
      clearedPoleNumerator a e l j := by
    apply dvd_mul_of_dvd_right
    exact Finset.dvd_prod_of_mem
      (fun q : ι ↦ (Polynomial.X - Polynomial.C (a q)) ^ (e q + 1)) hmem
  have hshift : (PowerSeries.X : PowerSeries F) ^ (e i + 1) ∣
      bennettShiftToSeries (a i) (clearedPoleNumerator a e l j) := by
    simpa only [map_pow, bennettShiftToSeries_linear, sub_self, map_zero, zero_add]
      using map_dvd (bennettShiftToSeries (a i)) hdiv
  exact PowerSeries.X_pow_dvd_iff.mp
    (dvd_mul_of_dvd_left hshift (bennettLocalReciprocal a e i)) (e i) (Nat.lt_succ_self _)







end Field

end D1Bound5
end
