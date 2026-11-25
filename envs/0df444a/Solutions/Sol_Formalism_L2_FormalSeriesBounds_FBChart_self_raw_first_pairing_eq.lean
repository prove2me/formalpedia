-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.self_raw_first_pairing_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:50:11.307538+00:00
-- url     : https://prove2.me/submissions/da4ca006-cd44-4aab-8fc9-2af29d8006e8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStabSelf
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_E2_sum_hCol_eq_ite

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
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I0 : Type} [Fintype I0]
namespace Formalism.L2.FormalSeriesBounds
namespace FBChart
theorem _root_.solution (Y : FBChart C V O dd) (p : SelfData Y d I0) (w v : Fin 2 × Fin dd → C) :
    (Y.rawSelf p).sg1 w v = -∑ col, bil Y.h (fun i => w (col, i)) (fun j => v (col, j)) := by
  have hsg : ∀ x : Fin 2 × Fin dd, MvPowerSeries.coeff (Finsupp.single x 1) ((Y.rawSelf p).sg v) =
      -∑ i : Fin 2 × Fin dd, v i *
        (if x.1 = i.1 then MvPowerSeries.coeff (E2 ((0 : Fin 2), x.2) ((1 : Fin 2), i.2)) Y.h else 0) := by
    intro x
    show (-∑ i, v i * MvPowerSeries.coeff ((Finsupp.single x 1).mapDomain (fun y => ((0 : Fin 2), y)) +
      Finsupp.single ((1 : Fin 2), i) 1) (∑ col, hCol col Y.h)) = _
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.mapDomain_single]
    rw [show Finsupp.single ((0 : Fin 2), x) 1 + Finsupp.single ((1 : Fin 2), i) 1 =
      E2 ((0 : Fin 2), (x.1, x.2)) ((1 : Fin 2), (i.1, i.2)) from rfl, coeff_E2_sum_hCol_eq_ite]
  simp only [RawChart.sg1, hsg, bil, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, if_true, zero_ne_one, one_ne_zero, if_false, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_add]
  congr 1 <;> (congr 1; exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
end FBChart
end Formalism.L2.FormalSeriesBounds
