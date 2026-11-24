-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.pht_window_sum_Ico_telescope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:40:59.710871+00:00
-- url     : https://prove2.me/submissions/6ce4dd71-cba7-4a2f-8af5-cc0741e0a670

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window

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
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution (f : ℤ → ℤ) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, (f a - f (a + 1)) = f m - f k := by
  induction k, hmk using Int.le_induction with
  | base => simp
  | succ k hk ih =>
    have hs : Finset.Ico m (k + 1) = insert k (Finset.Ico m k) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hs, Finset.sum_insert (by simp), ih]
    ring
end Formalism.WeaklyAdmissibleFiltrations
