-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.cc_hAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:46:31.63601+00:00
-- url     : https://prove2.me/submissions/45e1d758-5040-40b6-8336-32c5332d08f2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_constantCoeff_pair_substitution
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_h
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_subst


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) : MvPowerSeries.constantCoeff (hAt Y a b) = 0 := by
  unfold hAt
  exact VP.cc_subst (constantCoeff_pair_substitution ha hb) (cc_h Y)
end Formalism.L2.FormalSeriesBounds.VP
