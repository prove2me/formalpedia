-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.square_moment_from_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:47.193779+00:00
-- url     : https://prove2.me/submissions/c3292252-d12e-48fc-b23d-00d31c1a02ad

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
theorem _root_.solution : Sqm_from := by
  intro C₀ L logT logg b' m N hC hL hm hT hg hb
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL0 : 0 ≤ L := by linarith
  have h1 : L ≤ m * L := by nlinarith
  have h2 : C₀ * L ≤ C₀ * m * L := by nlinarith [mul_nonneg hC hL0]
  have hs : L + logT + logg ≤ (1 + 2 * C₀) * m * L := by nlinarith
  have hmN : 0 ≤ (m : ℝ) ^ 2 * (N : ℝ) ^ 2 := by positivity
  have hNL : 0 ≤ (N : ℝ) * L := by positivity
  calc (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) ≤ (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * ((1 + 2 * C₀) * m * L) :=
        mul_le_mul_of_nonneg_left hs hmN
    _ = (N * L) * ((1 + 2 * C₀) * (m : ℝ) ^ 3 * N) := by ring
    _ ≤ (N * L) * b' := mul_le_mul_of_nonneg_left hb hNL
    _ = N * b' * L := by ring
end Formalism.HermitianLattices.TraceIntegrality
