-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.negativeJumpsSum_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:40:54.493078+00:00
-- url     : https://prove2.me/submissions/b0dcc664-2595-48cc-9d8d-8576214d7d5b

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_DpcrisStable
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_NegJumps
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
private theorem negJumps_Ico_telescope (f : ℤ → ℤ) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, (f a - f (a + 1)) = f m - f k := by
  induction k, hmk using Int.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [← Finset.Ico_union_Ico_eq_Ico hk (by omega),
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive m k (k + 1)), ih]
    have h1 : Finset.Ico k (k + 1) = {k} := by
      ext z
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [h1, Finset.sum_singleton]
    ring
end Formalism.WeaklyAdmissibleFiltrations
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : NegJumps := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ τ lo _ hlo hF
  have h1 := negJumps_Ico_telescope (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) lo 0 hlo
  unfold multV
  rw [h1, hF]
end Formalism.WeaklyAdmissibleFiltrations
