-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.sums_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:27.957797+00:00
-- url     : https://prove2.me/submissions/cc73805e-519e-4136-95d4-f488418a5d02

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution (xs : List (ℕ × Bool)) : leftSum xs + rightSum xs = (xs.map Prod.fst).sum := by
  induction xs with
  | nil => simp [leftSum, rightSum]
  | cons p xs ih =>
    obtain ⟨w, b⟩ := p
    cases b <;> simp [leftSum, rightSum] at * <;> omega
end CSeparatedNPComplete.PolynomialCertificate
