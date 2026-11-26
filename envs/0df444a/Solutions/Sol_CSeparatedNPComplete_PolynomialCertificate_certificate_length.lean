-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.certificate_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:01.045642+00:00
-- url     : https://prove2.me/submissions/33068ea3-0891-4de9-ae27-42643b1488d7

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution {n : ℕ} (b : Fin n → Bool) : (certificate b).length = n := by
  simp [certificate]
end CSeparatedNPComplete.PolynomialCertificate
