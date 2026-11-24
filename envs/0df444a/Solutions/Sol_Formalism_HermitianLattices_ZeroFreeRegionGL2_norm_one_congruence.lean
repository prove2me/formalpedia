-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.norm_one_congruence
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:37.05005+00:00
-- url     : https://prove2.me/submissions/f56b17af-2644-4031-a3c3-b4c694248cb8

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : NormOneCongr := by
  intro d N p h
  have key : ((p : ℤ) ≡ 1 [ZMOD (N : ℤ)]) := by
    obtain ⟨u, v, ⟨a, ha⟩, ⟨b, hb⟩, h⟩ := h
    have hu : u = 1 + N * a := by linarith
    rw [h, hu, hb]
    apply Int.modEq_iff_dvd.2
    refine ⟨-(2 * a + N * a ^ 2 + b + N * a * b + (((d + 1) / 4 : ℕ) : ℤ) * N * b ^ 2), ?_⟩
    ring
  refine ⟨key, fun χ => ?_⟩
  have : ((p : ℕ) : ZMod N) = 1 := by
    have := (ZMod.intCast_eq_intCast_iff (p : ℤ) 1 N).2 key
    simpa using this
  rw [this, map_one]
end Formalism.HermitianLattices.ZeroFreeRegionGL2
