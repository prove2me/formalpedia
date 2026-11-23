-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.logy_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:31.350898+00:00
-- url     : https://prove2.me/submissions/b2c0e3f6-ea91-4e4c-9b35-51b632d178d4

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTBAsmA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {cA M y : ℝ} (hcA : 0 < cA) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) : cA ^ 2 * Real.log y < Real.log M ^ 2 := by
  have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hs := Real.sq_sqrt hl
  have h0 : 0 ≤ cA * Real.sqrt (Real.log y) := by positivity
  have h2 : (cA * Real.sqrt (Real.log y)) ^ 2 < Real.log M ^ 2 := by nlinarith
  calc cA ^ 2 * Real.log y = (cA * Real.sqrt (Real.log y)) ^ 2 := by rw [mul_pow, hs]
    _ < Real.log M ^ 2 := h2
end Formalism.HermitianLattices.Ext.PrimesInProgressions
