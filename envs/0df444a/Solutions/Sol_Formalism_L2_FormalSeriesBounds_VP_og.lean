-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.og
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:34:59.551155+00:00
-- url     : https://prove2.me/submissions/c2200253-e308-4883-9f13-bace61ff764e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
import Definitions.Def_Formalism_DropLevelBounds_ConstantCoeffVanishing_UbintConstantCoeffEqZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
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
theorem _root_.solution {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (s : σ) :
    Formalism.BaseCaseIdentities.OrdGE 1 (a s) := by
  unfold Formalism.BaseCaseIdentities.OrdGE
  intro A hA
  have h0 : A = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]
    omega
  subst h0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact ha s
end Formalism.L2.FormalSeriesBounds.VP
