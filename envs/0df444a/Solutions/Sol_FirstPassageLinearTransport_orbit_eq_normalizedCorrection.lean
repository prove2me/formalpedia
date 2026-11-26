-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_eq_normalizedCorrection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:56.649097+00:00
-- url     : https://prove2.me/submissions/8ca4ac5a-a590-4037-8a93-d40d1170f350

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_normalizedCorrectionTerm_mul_pow
import Theorems.Thm_FirstPassageLinearTransport_exact_affine_iterate_real


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (k n : ℕ) :
    (orbit k n : ℝ) =
      ((n : ℝ) / (2 : ℝ) ^ k + normalizedCorrection k n) *
        (3 : ℝ) ^ oddCount n k := by
  rw [exact_affine_iterate_real]
  unfold normalizedCorrection
  calc
    (3 : ℝ) ^ oddCount n k / (2 : ℝ) ^ k * (n : ℝ) +
          ∑ i ∈ Finset.range k,
            parityDigitR n i *
              (3 : ℝ) ^ (oddCount n k - oddCount n (i + 1)) /
                (2 : ℝ) ^ (k - i) =
        (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount n k +
          ∑ i ∈ Finset.range k,
            normalizedCorrectionTerm k n i *
              (3 : ℝ) ^ oddCount n k := by
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro i hi
        exact (normalizedCorrectionTerm_mul_pow
          (Finset.mem_range.mp hi)).symm
    _ = ((n : ℝ) / (2 : ℝ) ^ k + normalizedCorrection k n) *
          (3 : ℝ) ^ oddCount n k := by
      unfold normalizedCorrection
      rw [add_mul, Finset.sum_mul]
end FirstPassageLinearTransport
