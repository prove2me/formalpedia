-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_sum_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:35.787798+00:00
-- url     : https://prove2.me/submissions/328871a7-36cb-4a5d-a0d2-ab5c883d7d8e

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Theorems.Thm_Formalism_QuantumDeterminants_gnExt_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℝ)
    (v : {i // 0 < lam i} → ℂ) (hv : v ≠ 0) :
    0 < ∑ i, lam i * Complex.normSq ((gnExt (fun i => 0 < lam i) *ᵥ v) i) := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (funext hcon)
  calc (0 : ℝ) = ∑ _i : ι, (0 : ℝ) := by simp
    _ < ∑ i, lam i * Complex.normSq ((gnExt (fun i => 0 < lam i) *ᵥ v) i) := by
        apply Finset.sum_lt_sum
        · intro i _
          rw [gnExt_mulVec]
          split_ifs with h
          · have := Complex.normSq_nonneg (v ⟨i, h⟩)
            nlinarith
          · simp
        · refine ⟨j.val, Finset.mem_univ _, ?_⟩
          rw [gnExt_mulVec, dif_pos j.property]
          have := Complex.normSq_pos.mpr (show v ⟨j.val, j.property⟩ ≠ 0 from hj)
          have hl := j.property
          nlinarith
end Formalism.QuantumDeterminants
