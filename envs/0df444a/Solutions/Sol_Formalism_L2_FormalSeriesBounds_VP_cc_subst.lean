-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.cc_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:06:49.517698+00:00
-- url     : https://prove2.me/submissions/7c01e2d8-bb77-44b2-8e79-329e874fcd4c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
import Definitions.Def_Formalism_DropLevelBounds_ConstantCoeffVanishing_UbintConstantCoeffEqZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_og
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_subst


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] {σ τ ρ : Type}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
  have h : Formalism.BaseCaseIdentities.OrdGE 1 (MvPowerSeries.subst a f) :=
    ordGE_subst (og ha) (og (a := fun _ : Unit => f) (fun _ => hf) ())
  have h0 := h 0 (by simp)
  rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
end Formalism.L2.FormalSeriesBounds.VP
