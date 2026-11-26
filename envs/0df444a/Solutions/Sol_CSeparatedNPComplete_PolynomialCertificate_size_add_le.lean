-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.size_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:46.781867+00:00
-- url     : https://prove2.me/submissions/1d94477a-19e9-43da-a940-5108e64ef91f

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution (x y : ℕ) : Nat.size (x + y) ≤ Nat.size x + Nat.size y + 1 := by
  apply Nat.size_le.mpr
  have hx := Nat.lt_size_self x
  have hy := Nat.lt_size_self y
  have hxp : 2 ^ Nat.size x ≤ 2 ^ (Nat.size x + Nat.size y) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hyp : 2 ^ Nat.size y ≤ 2 ^ (Nat.size x + Nat.size y) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ]
  omega
end CSeparatedNPComplete.PolynomialCertificate
