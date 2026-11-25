-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.gsum_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:20:05.92658+00:00
-- url     : https://prove2.me/submissions/507b6c16-d341-4ca4-ba2b-c48dd1bdeb58

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_pair_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_pair_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_gsum_const
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
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
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
namespace Formalism.L2.FormalSeriesBounds.FormalGermZero
theorem _root_.solution {σ ι : Type} (Y : FBChart C V O dd) (Γ : ι → Fin dd → MvPowerSeries σ C)
    (hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (hΓ : ∀ c j, IntS V (Γ c j)) :
    ∀ (l : List ι) j, IntS V (gsum Y.B.G.F Γ l j)
  | [], j => by
    intro μ
    show V.Ge 0 (MvPowerSeries.coeff μ ((0 : Fin dd → MvPowerSeries σ C) j))
    rw [Pi.zero_apply, map_zero]
    exact VF.Ge.zero 0
  | c :: l, j => IntS.subst (pair_const (hΓ0 c) (gsum_const Y Γ hΓ0 l))
      (pair_int (hΓ c) (solution Y Γ hΓ0 hΓ l)) (Y.intF j)
end Formalism.L2.FormalSeriesBounds.FormalGermZero
