-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.run_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:52.03245+00:00
-- url     : https://prove2.me/submissions/cf743494-1b6c-4d52-8f9c-72481c502a22

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution (xs : List (ℕ × Bool)) :
    (run xs).leftCount = leftCount xs ∧ (run xs).rightCount = rightCount xs ∧
    (run xs).leftSum = leftSum xs ∧ (run xs).rightSum = rightSum xs := by
  induction xs with
  | nil => simp [run, leftCount, rightCount, leftSum, rightSum]
  | cons p xs ih =>
    obtain ⟨w, b⟩ := p
    cases b <;> simp [run, leftCount, rightCount, leftSum, rightSum,
      leftCount, rightCount, leftSum, rightSum] at * <;> omega
end CSeparatedNPComplete.PolynomialCertificate
