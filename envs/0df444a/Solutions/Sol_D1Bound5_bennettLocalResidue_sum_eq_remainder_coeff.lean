-- Prove2me | solution 1 for D1Bound5.bennettLocalResidue_sum_eq_remainder_coeff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:26.28797+00:00
-- url     : https://prove2.me/submissions/a58b54e3-f00d-45a8-a448-e12ffcb3a54d

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettPartialFractions_Definitions
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions
import Theorems.Thm_D1Bound5_bennettLocalResidue_eq_decomposition_coeff
import Theorems.Thm_D1Bound5_bennettLocalResidue_eq_zero_of_denominator_dvd
import Theorems.Thm_D1Bound5_bennettPoleDenominator_degree
import Theorems.Thm_D1Bound5_bennettPoleDenominator_monic
import Theorems.Thm_D1Bound5_coeff_eq_sum_simple_residues
import Theorems.Thm_D1Bound5_exists_clearedPole_decomposition

section
open Finset Polynomial

namespace D1Bound5

section Reverse

variable {F : Type*} [Field F]



end Reverse

section Residues

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]



theorem bennettLocalResidue_add (a : ι → F) (e : ι → ℕ)
    (f g : F[X]) (i : ι) :
    bennettLocalResidue a e (f + g) i =
      bennettLocalResidue a e f i + bennettLocalResidue a e g i := by
  simp only [bennettLocalResidue, map_add, add_mul]

/-- For an arbitrary numerator, the sum of the actual local residues is the
coefficient one below the denominator degree in its polynomial remainder.
The required proper partial fractions are constructed, not assumed. -/
theorem _root_.solution
    (a : ι → F) (ha : Function.Injective a) (e : ι → ℕ) (f : F[X]) :
    ∑ i, bennettLocalResidue a e f i =
      (f %ₘ bennettPoleDenominator a e).coeff ((∑ i, (e i + 1)) - 1) := by
  let D := bennettPoleDenominator a e
  let r := f %ₘ D
  have hrem : r.degree < (∑ i, (e i + 1) : ℕ) := by
    have h := Polynomial.degree_modByMonic_lt f (bennettPoleDenominator_monic a e)
    simpa only [bennettPoleDenominator_degree] using h
  obtain ⟨c, hc⟩ := exists_clearedPole_decomposition a ha e r hrem
  have hlocal (i : ι) : bennettLocalResidue a e f i =
      bennettLocalResidue a e r i := by
    calc
      _ = bennettLocalResidue a e (r + D * (f /ₘ D)) i :=
        congrArg (fun p => bennettLocalResidue a e p i)
          (Polynomial.modByMonic_add_div f D).symm
      _ = _ := by
        rw [bennettLocalResidue_add,
          bennettLocalResidue_eq_zero_of_denominator_dvd a e _ (dvd_mul_right D _) i,
          add_zero]
  calc
    _ = ∑ i, bennettLocalResidue a e r i := Finset.sum_congr rfl (fun i _ => hlocal i)
    _ = ∑ i, c i (Fin.last (e i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact bennettLocalResidue_eq_decomposition_coeff a ha e c r hc i
    _ = _ := (coeff_eq_sum_simple_residues a e c r hc).symm











end Residues

end D1Bound5
end
