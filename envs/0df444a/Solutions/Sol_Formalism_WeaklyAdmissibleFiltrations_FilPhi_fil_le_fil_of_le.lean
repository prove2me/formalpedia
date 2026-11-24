-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.FilPhi.fil_le_fil_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:41:02.684283+00:00
-- url     : https://prove2.me/submissions/4bfc8683-89e4-4136-bf3f-bd6a972602bd

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_JumpsPFilAntitoneOfLe

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
open Formalism.WeaklyAdmissibleFiltrations.FilPhi
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]
namespace Formalism.WeaklyAdmissibleFiltrations.FilPhi
theorem _root_.solution (F : FilPhi LL D n Emb) (τ : Emb) {b a : ℤ} (hba : b ≤ a) :
    F.Fil τ a ≤ F.Fil τ b := by
  induction a, hba using Int.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact (F.Fil_anti τ k).trans ih
end Formalism.WeaklyAdmissibleFiltrations.FilPhi
