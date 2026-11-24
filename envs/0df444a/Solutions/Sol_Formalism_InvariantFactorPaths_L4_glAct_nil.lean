-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.glAct_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:58:11.020207+00:00
-- url     : https://prove2.me/submissions/98c5ba02-d644-4fad-aca9-df8742dbd2d3

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_keep
import Theorems.Thm_Formalism_CountingSumsFrames_wt_shift
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_abs_wt_le
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_sum_shift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {N : ℕ} (LL : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d)
    (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ∃ n : ℕ, ((glAct p LL j c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ^ n) h = 0 := by
  classical
  set D := h.totalDegree with hD
  let Q : ℕ → Set (Fin N × Fin r →₀ ℕ) := fun k => {m | ∑ v, m v ≤ D ∧ (k : ℤ) - D ≤ wt LL j c m}
  have h0 : h ∈ restrictSupport ℚ_[p] (Q 0) := by
    rw [mem_restrictSupport_iff]
    intro m hm
    have h1 : ∑ v, m v ≤ D := by
      have := le_totalDegree (Finset.mem_coe.mp hm)
      rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    refine ⟨h1, ?_⟩
    have h2 := abs_le.mp (abs_wt_le LL j c m)
    have h3 : ((∑ v, m v : ℕ) : ℤ) ≤ D := by exact_mod_cast h1
    push_cast at h2 h3 ⊢
    linarith [h2.1]
  have hs : ∀ k, ∀ x ∈ restrictSupport ℚ_[p] (Q k), glAct p LL j c d x ∈ restrictSupport ℚ_[p] (Q (k + 1)) := by
    intro k
    refine glAct_keep LL j c d _ _ ?_ ?_
    · intro i hi hv m hm hb
      refine ⟨by rw [sum_shift m _ _ hb]; exact hm.1, ?_⟩
      rw [(wt_shift LL j c d c i hi m).1 hv hb, if_pos rfl, if_neg (Ne.symm hcd)]
      have := hm.2
      push_cast
      linarith
    · intro i hi hv m hm hb
      refine ⟨by rw [sum_shift m _ _ hb]; exact hm.1, ?_⟩
      rw [(wt_shift LL j c d c i hi m).2 hv hb, if_pos rfl, if_neg (Ne.symm hcd)]
      have := hm.2
      push_cast
      linarith
  have hk : ∀ k, ((glAct p LL j c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ^ k) h ∈
      restrictSupport ℚ_[p] (Q k) := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hs k _ ih
  refine ⟨2 * D + 1, ?_⟩
  by_contra hne
  obtain ⟨m, hm⟩ := support_nonempty.mpr hne
  have h1 := hk (2 * D + 1)
  rw [mem_restrictSupport_iff] at h1
  replace h1 := h1 (Finset.mem_coe.mpr hm)
  have h2 := abs_le.mp (abs_wt_le LL j c m)
  have h3 : ((∑ v, m v : ℕ) : ℤ) ≤ D := by exact_mod_cast h1.1
  have h4 := h1.2
  push_cast at h2 h3 h4
  linarith [h2.2]
end Formalism.InvariantFactorPaths.L4
