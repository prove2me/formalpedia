-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.subst_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:05:02.773326+00:00
-- url     : https://prove2.me/submissions/ddc8e776-e43f-41bf-b1a3-66fec418bc65

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
theorem _root_.solution [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (c : C) (f : MvPowerSeries σ C) :
    MvPowerSeries.subst a (c • f) = c • MvPowerSeries.subst a f := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_smul _ c f
end Formalism.L2.FormalSeriesBounds.VP
