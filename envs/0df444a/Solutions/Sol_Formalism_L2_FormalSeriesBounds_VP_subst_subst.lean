-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.subst_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:58:41.367851+00:00
-- url     : https://prove2.me/submissions/f57cfbdb-d7b5-4710-8c7f-986dc557cc1f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
import Definitions.Def_Formalism_DropLevelBounds_ConstantCoeffVanishing_UbintConstantCoeffEqZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_hs
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
theorem _root_.solution [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C} {b : τ → MvPowerSeries ρ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : MvPowerSeries σ C) :
    MvPowerSeries.subst b (MvPowerSeries.subst a f) =
      MvPowerSeries.subst (fun s => MvPowerSeries.subst b (a s)) f := MvPowerSeries.subst_comp_subst_apply (hs ha) (hs hb) f
end Formalism.L2.FormalSeriesBounds.VP
