-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.pderiv_l_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:27:11.69447+00:00
-- url     : https://prove2.me/submissions/5e83ad86-eca0-48d0-a9c5-0b2d26d2885d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (m i : Fin dd) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv C i (l Y m)) = if m = i then 1 else 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp only [Finsupp.coe_zero, Pi.zero_apply, zero_add, Nat.cast_zero, Nat.cast_one, one_mul, mul_one]
  change MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) (Finsupp.single i 1))
    (Y.lg m) = _
  rw [Finsupp.mapDomain_single, Y.lg_lin m _ (by simp), MvPowerSeries.coeff_X]
  by_cases hmi : m = i
  · subst hmi; simp
  · rw [if_neg hmi, if_neg]
    intro h
    have := Finsupp.single_left_injective (one_ne_zero) h
    exact hmi (congrArg Prod.snd this).symm
end Formalism.L2.FormalSeriesBounds.VP
