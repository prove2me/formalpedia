-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.base_case_k_one_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:39:33.499847+00:00
-- url     : https://prove2.me/submissions/9c567fee-8afe-4e18-9724-c820e03ed86a

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
namespace Formalism.BaseCaseIdentities
namespace Data
theorem _root_.solution {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C]
    (D : Data k Z C) : D.FrobeniusBaseCaseIdentity := by
  intro hi
  have hK : D.K = 1 := by simp [Data.K, Kn, hi]
  have hzero : ∀ w : ℝ, D.Wt w (0 : MvPowerSeries Z k) := by
    intro w A
    simp
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [hK] at hc
    have : D.lev c = 0 := by omega
    rw [this]
    show D.Wt D.top (D.zvec c - D.zvec c)
    rw [sub_self]
    exact hzero _
  · intro c hc
    rw [hK] at hc
    have : D.zvec c = 0 := by
      unfold Data.zvec
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg]
      rintro rfl
      rw [D.ι_lev] at hc
      omega
    rw [this]
    exact hzero _
end Data
end Formalism.BaseCaseIdentities
