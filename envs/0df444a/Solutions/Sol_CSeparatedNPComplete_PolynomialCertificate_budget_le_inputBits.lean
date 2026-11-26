-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.budget_le_inputBits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:02.029805+00:00
-- url     : https://prove2.me/submissions/e3e1329a-94ff-48de-97b4-f5ab947d92f4

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    budget (tagged s b) ≤ 3 * inputBits s := by
  simp only [budget, tagged, List.map_ofFn, List.sum_ofFn, inputBits,
    ← mul_assoc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  dsimp
  omega
end CSeparatedNPComplete.PolynomialCertificate
