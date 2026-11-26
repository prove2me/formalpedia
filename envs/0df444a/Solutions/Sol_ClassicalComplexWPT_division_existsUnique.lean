-- Prove2me | solution 1 for ClassicalComplexWPT.division_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:16:52.132919+00:00
-- url     : https://prove2.me/submissions/37cbc5bb-6a29-43aa-9467-8dfe185e9e40

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_division_factorization
import Theorems.Thm_ClassicalComplexWPT_divisionQuotient_unique
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero



set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p : L1Coeff (A × ℕ)) (hp : ‖p‖ < 1)
    (f : L1Coeff (A × ℕ)) :
    ∃! qr : L1Coeff (A × ℕ) × L1Coeff (A × ℕ),
      f = lowShift d qr.1 + convolution qr.1 p + qr.2 ∧ highShift d qr.2 = 0 := by
  let q := divisionQuotient d p hp f
  let r := divisionRemainder d p hp f
  refine ⟨(q,r), ⟨division_factorization d p hp f, highShift_divisionRemainder d p hp f⟩, ?_⟩
  rintro ⟨q',r'⟩ ⟨hfac',hr'⟩
  have hq : q' = q := divisionQuotient_unique d p hp f q' r' hfac' hr'
  subst q'
  have hfac := division_factorization d p hp f
  have heq : (lowShift d q + convolution q p) + r =
      (lowShift d q + convolution q p) + r' := by
    simpa only [add_assoc] using hfac.symm.trans hfac'
  have hr_eq : r = r' := add_left_cancel heq
  subst r'
  rfl
end ClassicalComplexWPT
