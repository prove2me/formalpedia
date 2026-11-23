-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.first_zeta_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:17.779813+00:00
-- url     : https://prove2.me/submissions/8d70492e-92ab-4b43-9597-3d64d00b21c0

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
theorem _root_.solution : PackingCountBound := by
  intro f g u v hf hv hu
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hfv : 0 < (f : ℝ) / v := div_pos (by linarith) hv
  set t := 2 * Real.sqrt u / Real.sqrt (f / v) with ht
  have ht2 : t ^ 2 = 4 * u * v / f := by
    rw [ht, div_pow, mul_pow, Real.sq_sqrt hu, Real.sq_sqrt hfv.le]
    field_simp
    ring
  have huv : 0 ≤ 4 * u * v := by positivity
  have ht2' : t ^ 2 ≤ 4 * u * v := by
    rw [ht2]; exact div_le_self huv hfR
  have key : (1 + t) ^ 2 ≤ 2 * (1 + 4 * u * v) := by nlinarith [sq_nonneg (1 - t)]
  calc (1 + t) ^ (2 * g) = ((1 + t) ^ 2) ^ g := pow_mul _ _ _
    _ ≤ (2 * (1 + 4 * u * v)) ^ g := pow_le_pow_left₀ (sq_nonneg _) key g
    _ = 2 ^ g * (1 + 4 * u * v) ^ g := mul_pow _ _ _
end Formalism.HermitianLattices.TraceIntegrality
