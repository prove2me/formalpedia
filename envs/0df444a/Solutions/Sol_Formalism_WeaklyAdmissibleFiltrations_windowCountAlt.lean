-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.windowCountAlt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:07.972208+00:00
-- url     : https://prove2.me/submissions/b2b6dc94-02c6-42c4-aa4b-dc1f3da96136

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_WindowCount
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_WindowCountIcoTelescope
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.WeaklyAdmissibleFiltrations
open Module
private theorem windowCount_Ico_telescope (f : ℤ → ℤ) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, (f a - f (a + 1)) = f m - f k := by
  induction k, hmk using Int.le_induction with
  | base => simp
  | succ k hk ih =>
    have hset : Finset.Ico m (k + 1) = insert k (Finset.Ico m k) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hset, Finset.sum_insert (by simp), ih]
    ring
end Formalism.WeaklyAdmissibleFiltrations
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : WindowCount := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ τ lo hi hlh
  unfold multV
  exact windowCount_Ico_telescope (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) lo hi hlh
end Formalism.WeaklyAdmissibleFiltrations
