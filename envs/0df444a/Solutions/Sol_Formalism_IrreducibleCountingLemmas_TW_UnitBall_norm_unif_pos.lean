-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.UnitBall.norm_unif_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:29.100313+00:00
-- url     : https://prove2.me/submissions/832681c8-fe69-4017-9cb0-9c9c21136dd8

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWUnitBallLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.UnitBall
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace Formalism.IrreducibleCountingLemmas.TW.UnitBall
theorem _root_.solution (ϖ : K) (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n) : 0 < ‖ϖ‖ := by
  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
    linarith
  obtain ⟨n, hn⟩ := hd x hx0
  by_contra h
  have h0 : ‖ϖ‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
  rw [h0] at hn
  rcases eq_or_ne n 0 with rfl | hn0
  · simp at hn; linarith
  · rw [zero_zpow _ hn0] at hn; linarith
end Formalism.IrreducibleCountingLemmas.TW.UnitBall
