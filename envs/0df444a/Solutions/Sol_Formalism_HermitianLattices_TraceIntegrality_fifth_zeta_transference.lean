-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.fifth_zeta_transference
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:46.34426+00:00
-- url     : https://prove2.me/submissions/c0895175-1c8f-447e-9f4f-3075e827fda0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareMomentFromBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : LastMinimumSqBoundOfProductBound := by
  intro f k v l1 ln hf hv hl1 hln h hl
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hv2 : 0 < (2 * v) ^ 2 := by positivity
  have h1 : (ln * l1) ^ 2 ≤ (2 * f * k) ^ 2 := pow_le_pow_left₀ (mul_nonneg hln hl1) h 2
  have h2 : ln ^ 2 * ((f : ℝ) / (2 * v) ^ 2) ≤ ln ^ 2 * l1 ^ 2 := mul_le_mul_of_nonneg_left hl (sq_nonneg _)
  have h3 : ln ^ 2 * (f : ℝ) / (2 * v) ^ 2 ≤ 4 * f ^ 2 * k ^ 2 := by
    rw [mul_div_assoc]
    calc ln ^ 2 * ((f : ℝ) / (2 * v) ^ 2) ≤ ln ^ 2 * l1 ^ 2 := h2
      _ = (ln * l1) ^ 2 := by ring
      _ ≤ (2 * f * k) ^ 2 := h1
      _ = 4 * f ^ 2 * k ^ 2 := by ring
  rw [div_le_iff₀ hv2] at h3
  have hf0 : (0 : ℝ) < f := by linarith
  refine le_of_mul_le_mul_right ?_ hf0
  calc ln ^ 2 * (f : ℝ) ≤ 4 * f ^ 2 * k ^ 2 * (2 * v) ^ 2 := h3
    _ = 16 * f * (k : ℝ) ^ 2 * v ^ 2 * f := by ring
end Formalism.HermitianLattices.TraceIntegrality
