-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.gammaGradedStep_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:15.714824+00:00
-- url     : https://prove2.me/submissions/a72a5ff4-4d64-43b6-a4e3-f2b60b39459d

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
namespace Formalism.CoboundaryTransfers
theorem _root_.solution : GradedStep := by
  intro O A _ _ _ B M D _ _ _ _ W u hu i n hn
  obtain ⟨t, ht⟩ := hu
  obtain ⟨n', hn', hγ⟩ := W.γ_N n hn
  have hw : ∀ k : ℕ, ∃ r : A, (algebraMap O A u + B.X * t) ^ k
      = algebraMap O A (u ^ k) + B.X * r := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * (algebraMap O A u + B.X * t) + algebraMap O A (u ^ k) * t, ?_⟩
      rw [pow_succ, hr, pow_succ, map_mul]; ring
  obtain ⟨r, hr⟩ := hw i
  have hγn : W.γ n = n + B.X • n' := by rw [← hγ]; abel
  refine ⟨r • n + (algebraMap O A u + B.X * t) ^ i • n', ?_, ?_⟩
  · exact W.N.add_mem (W.N.smul_mem _ hn) (W.N.smul_mem _ hn')
  · rw [W.γ_smul, map_pow, ht, mul_pow, hγn, hr,
      ← algebraMap_smul A (u ^ i) (B.X ^ i • n)]
    module
end Formalism.CoboundaryTransfers
