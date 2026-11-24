-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.div_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:52.420329+00:00
-- url     : https://prove2.me/submissions/48013a37-2614-4c7e-9222-fcbab0182772

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBCard
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBDivides
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRExcludedCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (Y M : ℝ) (hY : 1 ≤ Y) (hM : 0 < M) (h : Y < M ^ 4) :
    Y / M ≤ Y ^ ((3 : ℝ) / 4) := by
  have hY0 : 0 < Y := by linarith
  have h1 : Y ^ ((1 : ℝ) / 4) ≤ M := by
    by_contra hcon
    push Not at hcon
    have h4 := pow_le_pow_left₀ hM.le hcon.le 4
    have h5 : (Y ^ ((1 : ℝ) / 4)) ^ 4 = Y := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
      norm_num
    rw [h5] at h4
    linarith
  have h2 : Y = Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hY0]; norm_num
  rw [div_le_iff₀ hM]
  calc Y = Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) := h2
    _ ≤ Y ^ ((3 : ℝ) / 4) * M := by
        exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hY0.le _)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
