-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_rename_outside
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:16:23.822158+00:00
-- url     : https://prove2.me/submissions/6371fab3-2ff4-4332-a5ec-f260a706cc96

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStabSelf
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_rename_out


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (ν : τ →₀ ℕ) {s : τ}
    (hs : ν s ≠ 0) (hr : ∀ x, φ x ≠ s) :
    coeff ν (MvPowerSeries.subst (fun x => (X (φ x) : MvPowerSeries τ C)) F) = 0 := by
  refine coeff_subst_rename_out φ F ν fun e' he => hs ?_
  rw [← he]
  exact Finsupp.mapDomain_notin_range _ _ (by rintro ⟨x, hx⟩; exact hr x hx)
end Formalism.L2.FormalSeriesBounds
