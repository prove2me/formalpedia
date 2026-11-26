-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.encodeInput_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:54.627913+00:00
-- url     : https://prove2.me/submissions/413fb54c-903a-435d-a365-ce498877856c

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution {n : ℕ} (s : Fin n → ℕ) :
    (encodeInput s).length = inputBits s := by
  simp [encodeInput, encodeWeight, List.length_flatMap, List.map_ofFn,
    List.sum_ofFn, Nat.size_eq_bits_len, inputBits, Finset.mul_sum, mul_add]
  apply Finset.sum_congr rfl
  intro i _
  ring
end CSeparatedNPComplete.PolynomialCertificate
