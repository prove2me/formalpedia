-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.gsum_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:07:11.636811+00:00
-- url     : https://prove2.me/submissions/79271b75-c492-4313-929c-cdb7d39ded4b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_pair_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_subst_zero


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
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
namespace Formalism.L2.FormalSeriesBounds.FormalGermZero
theorem _root_.solution {σ ι : Type} (Y : FBChart C V O dd) (Γ : ι → Fin dd → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) :
    ∀ (l : List ι) j, MvPowerSeries.constantCoeff (gsum Y.B.G.F Γ l j) = 0
  | [], j => by
    show MvPowerSeries.constantCoeff ((0 : Fin dd → MvPowerSeries σ C) j) = 0
    simp
  | c :: l, j => constantCoeff_subst_zero (pair_const (hΓ c) (solution Y Γ hΓ l)) (Y.B.G.const j)
end Formalism.L2.FormalSeriesBounds.FormalGermZero
