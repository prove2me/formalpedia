-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.hyps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:59:11.898124+00:00
-- url     : https://prove2.me/submissions/c18a4eec-e0d4-450b-bdec-1b043666b26a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB

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
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d] {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]
namespace Formalism.L2.FormalSeriesBounds
namespace FBChart
theorem _root_.solution (hCart : CartFBSt) (hAx : AxesFBSt) (hG0 : IntegralGermIndependentAllCharts) (hC : CEqFBSt) (hR1 : IndependenceBoundAllCharts)
    (Y : FBChart C V O dd) (p : PairData Y d I) (hrk : (Y.raw p).RankHyp)
    (hR2 : RawChart.RankMaximalCondition (hCart C V O dd Y d I p)) (hCH : RawChart.CHSt (hCart C V O dd Y d I p)) :
    (Y.raw p).Hyps V where
  charZero := inferInstance
  algClosed := Y.algClosed
  l_odd := Y.l_odd
  k_unit := Y.k_unit
  cartH := hCart C V O dd Y d I p
  rank := hrk
  axes := hAx C V O dd Y d I p
  G0 := hG0 C V O dd Y d I p _
  CEq := hC C V O dd Y d I p hrk _
  R1 := hR1 C V O dd Y d I p hrk _ hR2
  R2 := hR2
  CH := hCH
end FBChart
end Formalism.L2.FormalSeriesBounds
