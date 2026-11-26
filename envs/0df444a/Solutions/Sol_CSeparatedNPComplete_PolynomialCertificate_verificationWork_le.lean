-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.verificationWork_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:57:56.468371+00:00
-- url     : https://prove2.me/submissions/c2d67dfb-a3d8-4756-a3ba-f5e19a726fb1

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_run_mass_le
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_run_work_le
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_dimension_le_inputBits
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_budget_le_inputBits

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    verificationWork s b ≤ 128 * (inputBits s + 1) ^ 2 := by
  have hr := run_work_le (tagged s b)
  have hm := run_mass_le (tagged s b)
  have hb := budget_le_inputBits s b
  have hn := dimension_le_inputBits s
  have hl : (tagged s b).length = n := by simp [tagged]
  rw [hl] at hr
  unfold verificationWork binaryCost
  dsimp [bitMass] at hm
  have hprod : n * (budget (tagged s b) + 1) ≤ inputBits s * (3 * inputBits s + 1) :=
    Nat.mul_le_mul hn (by omega)
  nlinarith
end CSeparatedNPComplete.PolynomialCertificate
