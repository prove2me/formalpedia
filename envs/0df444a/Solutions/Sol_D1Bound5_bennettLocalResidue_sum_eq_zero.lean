-- Prove2me | solution 1 for D1Bound5.bennettLocalResidue_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:11:55.598844+00:00
-- url     : https://prove2.me/submissions/7f3faf59-2998-4351-a296-2c240187bce0

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions
import Theorems.Thm_D1Bound5_bennettLocalResidue_eq_decomposition_coeff
import Theorems.Thm_D1Bound5_exists_clearedPole_decomposition_zero_residue_sum

section
open Finset

namespace D1Bound5

section Field

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]





















/-- The sum of the explicitly defined local residues vanishes whenever the
numerator has degree at least two below the full denominator degree.
No decomposition or cancellation identity is assumed. -/
theorem _root_.solution (a : ι → F) (ha : Function.Injective a)
    (e : ι → ℕ) (f : Polynomial F)
    (hdeg : f.degree < ((∑ l, (e l + 1)) - 1 : ℕ)) :
    ∑ i, bennettLocalResidue a e f i = 0 := by
  obtain ⟨c, hc, hsum⟩ :=
    exists_clearedPole_decomposition_zero_residue_sum a ha e f hdeg
  calc
    (∑ i, bennettLocalResidue a e f i) = ∑ i, c i (Fin.last (e i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact bennettLocalResidue_eq_decomposition_coeff a ha e c f hc i
    _ = 0 := hsum

end Field

end D1Bound5
end
