-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.multiplicitySum_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:55:27.586907+00:00
-- url     : https://prove2.me/submissions/c39e99cb-0e47-48aa-814b-b176865f33de

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pht_window_sum_Ico_telescope

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
theorem _root_.solution : DimSum := by
  intro LL _ D _ _ _ n Emb _ F D' τ
  have key : ∑ a ∈ Finset.Ico F.lo F.hi, ((finrank LL ↥(F.Fil τ a ⊓ D') : ℤ) -
      (finrank LL ↥(F.Fil τ (a + 1) ⊓ D') : ℤ)) =
      (finrank LL ↥(F.Fil τ F.lo ⊓ D') : ℤ) - (finrank LL ↥(F.Fil τ F.hi ⊓ D') : ℤ) :=
    pht_window_sum_Ico_telescope (fun a => (finrank LL ↥(F.Fil τ a ⊓ D') : ℤ)) F.lo F.hi F.lo_le
  unfold FilPhi.mult
  rw [key, F.Fil_lo τ F.lo le_rfl, F.Fil_hi τ F.hi le_rfl]
  simp
end Formalism.WeaklyAdmissibleFiltrations
