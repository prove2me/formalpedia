-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.counts_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:12.200802+00:00
-- url     : https://prove2.me/submissions/8b3cc9b9-5cf5-454a-b7fe-3c36949c8637

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution (xs : List (ℕ × Bool)) : leftCount xs + rightCount xs = xs.length := by
  induction xs with
  | nil => simp [leftCount, rightCount]
  | cons p xs ih =>
    obtain ⟨w, b⟩ := p
    cases b <;> simp [leftCount, rightCount] at * <;> omega
end CSeparatedNPComplete.PolynomialCertificate
