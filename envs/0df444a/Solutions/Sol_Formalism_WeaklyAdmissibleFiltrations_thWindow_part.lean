-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.thWindow_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:54:10.135574+00:00
-- url     : https://prove2.me/submissions/fcf3e2b8-e046-4962-8aad-643f0cafa0ab

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pht_window_mult_lo
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pht_window_mult_hi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : THWindow := by
  intro LL _ D _ _ _ n Emb _ F D' l h hl hh
  unfold FilPhi.tH FilPhi.tHw
  apply Finset.sum_congr rfl
  intro τ _
  symm
  apply Finset.sum_subset
  · intro a ha
    simp only [Finset.mem_Ico] at ha ⊢
    omega
  · intro a _ hna
    simp only [Finset.mem_Ico, not_and, not_lt] at hna
    rcases lt_or_ge a F.lo with h1 | h1
    · rw [pht_window_mult_lo F D' τ a h1, mul_zero]
    · rw [pht_window_mult_hi F D' τ a (hna h1), mul_zero]
end Formalism.WeaklyAdmissibleFiltrations
