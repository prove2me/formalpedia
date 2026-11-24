-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.exponent_total_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:44.823847+00:00
-- url     : https://prove2.me/submissions/f31acd84-0d83-4b6e-9d9a-9532e78b6149

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : ExponentTotalBound := by
  intro ι Ψ TT VV W bp m t f N C1 C2 e1 hV hm ht htN hf hC1 hC2 hW hb hWb he
  have hN : 1 ≤ N := by linarith
  set A := ∑ τ ∈ Ψ, W τ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg hW
  set Bs := ∑ τ ∈ TT, (bp τ + N) with hB
  have hB0 : 0 ≤ Bs := Finset.sum_nonneg (fun τ h => by linarith [hb τ h])
  have s1 : ∑ τ ∈ VV, (t + 1 + 2 * W τ + C2 * N) ≤ (C2 + 4) * Bs := by
    calc _ ≤ ∑ τ ∈ VV, (C2 + 4) * (bp τ + N) := by
          apply Finset.sum_le_sum
          intro τ h
          have := hWb τ h
          have := hb τ (hV h)
          nlinarith
      _ ≤ ∑ τ ∈ TT, (C2 + 4) * (bp τ + N) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hV
          intro τ h _
          have := hb τ h
          positivity
      _ = _ := by rw [Finset.mul_sum]
  have s2 : (∑ τ ∈ VV, (t + 1 + 2 * W τ + C2 * N)) * (m * (m + 1) / 2) ≤ (C2 + 4) * Bs * (m * m) := by
    calc _ ≤ (C2 + 4) * Bs * (m * (m + 1) / 2) := mul_le_mul_of_nonneg_right s1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have s3 : m * e1 ≤ m * (4 * A + C1 * f * N) := mul_le_mul_of_nonneg_left he (by linarith)
  have s4 : C1 * f * N * m ≤ C1 * f * N * (m * m) := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have p1 : 0 ≤ (C1 + C2 + 5) * m * A := by positivity
  have p2 : 0 ≤ (C2 + 9) * m * (f * m * N) := by positivity
  have p3 : 0 ≤ (C1 + 5) * m * (m * Bs) := by positivity
  nlinarith
end Formalism.HermitianLattices.LocalLatticeBases
