-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.gadget_polynomial_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:58.030617+00:00
-- url     : https://prove2.me/submissions/3bbd971e-ab8d-4c70-a87f-f5522fa81c31

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_certificate_length
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_dimension_le_inputBits
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_verificationWork_le
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_verify_iff_partition
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_binary_has_certificate
public import Theorems.Thm_CSeparatedNPComplete_partition_gadget_schedule_pointwise_iff


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution (d : ℕ) (s : Fin d → ℕ)
    (hd : 4 ≤ d) (hc : 1 ≤ dot (fun i => (s i : ℝ)) 1 / 2)
    (hs : perf_square_vec (fun i => (s i : ℝ))) :
    (∃ a : Vec d, box_constraints a ∧ dot a 1 = (d : ℝ) / 2 ∧
      hinge_form (dot (fun i => (s i : ℝ)) 1 / 2) a
        (partition_gadget_schedule d (fun i => (s i : ℝ))) ≤
        partition_schedule_threshold d (fun i => (s i : ℝ))) ↔
    ∃ b : Fin d → Bool, verify s b = true ∧
      (certificate b).length ≤ inputBits s ∧
      verificationWork s b ≤ 128 * (inputBits s + 1) ^ 2 := by
  constructor
  · rintro ⟨a, ha⟩
    have hp := (partition_gadget_schedule_pointwise_iff d a (fun i => (s i : ℝ)) hd hc hs).mp ha
    obtain ⟨b, hb⟩ := binary_has_certificate a hp.1
    refine ⟨b, (verify_iff_partition s b).mpr (by rwa [hb]), ?_, verificationWork_le s b⟩
    rw [certificate_length]
    exact dimension_le_inputBits s
  · rintro ⟨b, hb, _, _⟩
    exact ⟨selector b, (partition_gadget_schedule_pointwise_iff d (selector b)
      (fun i => (s i : ℝ)) hd hc hs).mpr ((verify_iff_partition s b).mp hb)⟩
end CSeparatedNPComplete.PolynomialCertificate
