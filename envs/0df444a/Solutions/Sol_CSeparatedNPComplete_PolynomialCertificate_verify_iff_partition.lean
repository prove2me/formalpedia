-- Prove2me | solution 1 for CSeparatedNPComplete.PolynomialCertificate.verify_iff_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:57:46.111231+00:00
-- url     : https://prove2.me/submissions/74add9ed-5370-4069-98f2-bf6e021977c8

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_run_correct
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_counts_total
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_sums_total
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_selector_binary
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_selector_count
public import Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_selector_sum

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate
namespace CSeparatedNPComplete.PolynomialCertificate
theorem _root_.solution {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    verify s b = true ↔ is_ec_partition (selector b) (fun i => (s i : ℝ)) := by
  obtain ⟨hlc, hrc, hls, hrs⟩ := run_correct (tagged s b)
  have hc : (leftCount (tagged s b) : ℝ) + (rightCount (tagged s b) : ℝ) = (n : ℝ) := by
    exact_mod_cast (show leftCount (tagged s b) + rightCount (tagged s b) = n by
      simpa [tagged] using counts_total (tagged s b))
  have hs : (leftSum (tagged s b) : ℝ) + (rightSum (tagged s b) : ℝ) =
      dot (fun i => (s i : ℝ)) 1 := by
    rw [← Nat.cast_add, sums_total]
    simp [tagged, dot, List.map_ofFn, List.sum_ofFn, Nat.cast_sum]
  simp only [verify, Bool.and_eq_true, beq_iff_eq, hlc, hrc, hls, hrs,
    is_ec_partition, selector_count s b, selector_sum]
  constructor
  · rintro ⟨hcount, hsum⟩
    have hcount' : (leftCount (tagged s b) : ℝ) = (rightCount (tagged s b) : ℝ) := by exact_mod_cast hcount
    have hsum' : (leftSum (tagged s b) : ℝ) = (rightSum (tagged s b) : ℝ) := by exact_mod_cast hsum
    exact ⟨selector_binary b, by linarith, by linarith⟩
  · rintro ⟨_, hcount, hsum⟩
    constructor
    · exact_mod_cast (show (leftCount (tagged s b) : ℝ) = (rightCount (tagged s b) : ℝ) by linarith)
    · exact_mod_cast (show (leftSum (tagged s b) : ℝ) = (rightSum (tagged s b) : ℝ) by linarith)
end CSeparatedNPComplete.PolynomialCertificate
