-- Prove2me | solution 1 for ClassicalComplexWPT.seqDivision_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:16:54.260167+00:00
-- url     : https://prove2.me/submissions/64d21d61-9758-40e4-8cb6-e941943d172f

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_seqDivisionPerturbationMap_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionOperatorInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionRhsInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainder
import Theorems.Thm_ClassicalComplexWPT_seqDivision_factorization
import Theorems.Thm_ClassicalComplexWPT_seqDivisionQuotient_unique
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero


attribute [local simp] ClassicalComplexWPT.seqDivisionPerturbationMap_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionOperatorInput_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionRhsInput_apply
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainder

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f : L1Coeff ℕ) :
    ∃! qr : L1Coeff ℕ × L1Coeff ℕ,
      f = seqLowShift d qr.1 + convolution qr.1 p + qr.2 ∧ seqHighShift d qr.2 = 0 := by
  let q := seqDivisionQuotient d p hp f
  let r := seqDivisionRemainder d p hp f
  refine ⟨(q,r), ⟨seqDivision_factorization d p hp f,
    seqHighShift_divisionRemainder d p hp f⟩, ?_⟩
  rintro ⟨q',r'⟩ ⟨hfac',hr'⟩
  have hq : q' = q := seqDivisionQuotient_unique d p hp f q' r' hfac' hr'
  subst q'
  have hfac := seqDivision_factorization d p hp f
  have heq : (seqLowShift d q + convolution q p) + r =
      (seqLowShift d q + convolution q p) + r' := by
    simpa only [add_assoc] using hfac.symm.trans hfac'
  have hr_eq : r = r' := add_left_cancel heq
  subst r'
  rfl
end ClassicalComplexWPT
