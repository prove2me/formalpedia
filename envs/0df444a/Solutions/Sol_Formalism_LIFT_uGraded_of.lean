-- Prove2me | solution 1 for Formalism.LIFT.uGraded_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:32:01.090207+00:00
-- url     : https://prove2.me/submissions/cd2848b3-3ea5-4ccf-b56c-e4dde765f08f

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_Graded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LIFT
namespace Formalism.LIFT
theorem _root_.solution (h : GradedStep) : UGraded := by
  intro ℓ _ A _ _ B M D _ _ _ _ W K
  induction K with
  | zero =>
    intro n hn
    exact ⟨0, W.N.zero_mem, n, hn, by simp⟩
  | succ K ih =>
    intro n hn
    obtain ⟨x, hx, n', hn', he⟩ := ih n hn
    obtain ⟨n'', hn'', hg⟩ := h ℓ A B M D W (K + 1) n' hn'
    refine ⟨((B.u : ℤ_[ℓ]) ^ (K + 1) - 1) • x + B.X ^ K • n', ?_, -n'', W.N.neg_mem hn'', ?_⟩
    · exact W.N.add_mem (Submodule.smul_of_tower_mem _ _ hx) (W.N.smul_mem _ hn')
    · rw [Finset.prod_Icc_succ_top (by omega), mul_comm, mul_smul, he]
      have e1 : B.X • (((B.u : ℤ_[ℓ]) ^ (K + 1) - 1) • x + B.X ^ K • n')
          = ((B.u : ℤ_[ℓ]) ^ (K + 1) - 1) • (B.X • x) + B.X ^ (K + 1) • n' := by
        rw [smul_add, smul_comm, ← mul_smul, ← pow_succ']
      rw [e1, LinearMap.map_add, LinearMap.map_smul]
      have e2 : W.γ (B.X ^ (K + 1) • n') = ((B.u : ℤ_[ℓ]) ^ (K + 1)) • (B.X ^ (K + 1) • n')
          + B.X ^ (K + 1 + 1) • n'' := by rw [← hg]; abel
      rw [e2]
      simp only [sub_smul, one_smul, smul_add, smul_sub, smul_neg]
      abel
end Formalism.LIFT
