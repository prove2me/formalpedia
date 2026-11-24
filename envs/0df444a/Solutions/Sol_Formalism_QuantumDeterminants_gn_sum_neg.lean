-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_sum_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:34.317238+00:00
-- url     : https://prove2.me/submissions/aff1602f-b28b-46b6-af78-567cf76f9237

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
    (v : {i // lam i < 0} → ℂ) (hv : v ≠ 0) :
    ∑ i, lam i * Complex.normSq ((gnExt (fun i => lam i < 0) *ᵥ v) i) < 0 := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (funext hcon)
  calc ∑ i, lam i * Complex.normSq ((gnExt (fun i => lam i < 0) *ᵥ v) i) < ∑ _i : ι, (0 : ℝ) := by
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
    _ = 0 := by simp
end Formalism.QuantumDeterminants
