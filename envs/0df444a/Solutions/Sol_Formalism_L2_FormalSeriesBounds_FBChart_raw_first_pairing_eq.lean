-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.raw_first_pairing_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:15.347805+00:00
-- url     : https://prove2.me/submissions/102981b9-54d7-4b5a-a9c8-2f849a6c6834

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab

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
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
namespace FBChart
theorem _root_.solution (Y : FBChart C V O dd) {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)
    (w v : Fin dd → C) : (Y.raw p).sg1 w v = -bil Y.h w v := by
  have hs : ∀ x, coeff (Finsupp.single x 1) ((Y.raw p).sg v) =
      -∑ i, v i * coeff (E2 ((0 : Fin 2), x) ((1 : Fin 2), i)) Y.h := by
    intro x
    show -∑ i, v i * coeff ((Finsupp.single x 1).mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) +
      Finsupp.single ((1 : Fin 2), i) 1) Y.h = _
    rw [Finsupp.mapDomain_single]
    rfl
  unfold RawChart.sg1 bil
  simp only [hs, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end FBChart
end Formalism.L2.FormalSeriesBounds
