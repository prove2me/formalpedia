-- Prove2me | solution 1 for Formalism.CL.W.gammaImageProduct_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:11.972637+00:00
-- url     : https://prove2.me/submissions/2b716535-4ef3-40e7-8d6e-d18b3388c7bf

import Definitions.Def_Formalism_WachModuleLifts_StatementW
import Definitions.Def_Formalism_WachModuleLifts_WachModuleProofs_WachModuleStatementHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CL Formalism.CL.W
namespace Formalism.CL.W
theorem _root_.solution : GammaOnto := by
  intro p _ A _ _ B η D _ _ _ _ W u a hyp
  suffices h : ∀ j, j ≤ a → ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      (∏ i ∈ Finset.Icc 1 j, (1 - u ^ i)) • (B.π₀ • n) =
        (W.γ (B.π₀ • x) - B.π₀ • x) + B.π₀ ^ (j + 1) • z' from h a le_rfl
  intro j
  induction j with
  | zero => intro _ n hn; exact ⟨0, W.N.zero_mem, n, hn, by simp⟩
  | succ j ih =>
    intro hj n hn
    obtain ⟨x, hx, m, hm, he⟩ := ih (by omega) n hn
    obtain ⟨n', hn', hg⟩ := hyp (j+1) (by omega) hj m hm
    refine ⟨(1 - u^(j+1)) • x - B.π₀ ^ j • m, ?_, n', hn', ?_⟩
    · exact W.N.sub_mem (W.N.smul_of_tower_mem _ hx) (W.N.smul_mem _ hm)
    · rw [Finset.prod_Icc_succ_top (by omega), mul_comm, mul_smul, he]
      have e1 : B.π₀ • ((1 - u^(j+1)) • x - B.π₀ ^ j • m)
          = (1 - u^(j+1)) • (B.π₀ • x) - B.π₀ ^ (j+1) • m := by
        rw [smul_sub, smul_comm, smul_smul, ← pow_succ']
      rw [e1, map_sub, LinearMap.map_smul, hg]
      have e2 : B.π₀ ^ (j + 1 + 1) • n' = B.π₀ ^ (j+1+1) • n' := rfl
      simp only [smul_sub, smul_add, sub_smul, one_smul]
      abel
end Formalism.CL.W
