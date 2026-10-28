-- Prove2me | solution 1 for D1Bound5.bennettLocalReciprocal_mul
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:35:01.39515+00:00
-- url     : https://prove2.me/submissions/4759703a-3d5d-4aec-bfc4-949eadecc819

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Theorems.Thm_D1Bound5_bennettPoleSeries_mul

section
open Finset

namespace D1Bound5

section Field

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]











theorem _root_.solution (a : ι → F) (ha : Function.Injective a)
    (e : ι → ℕ) (i : ι) :
    (∏ l ∈ (Finset.univ : Finset ι).erase i,
      (PowerSeries.C (a i - a l) + PowerSeries.X) ^ (e l + 1)) *
        bennettLocalReciprocal a e i = 1 := by
  unfold bennettLocalReciprocal
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro l hl
  apply bennettPoleSeries_mul
  exact sub_ne_zero.mpr (ha.ne (Finset.mem_erase.mp hl).1.symm)











end Field

end D1Bound5
end
