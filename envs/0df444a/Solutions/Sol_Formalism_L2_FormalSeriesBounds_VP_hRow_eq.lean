-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.hRow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:42.340783+00:00
-- url     : https://prove2.me/submissions/4a7c9186-1b44-436c-bc4f-adc93f35befd

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_TripleSubstSecondCoordinate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfBiadditiveCross

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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
open Formalism.L2.FormalSeriesBounds.VP
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (Y : FBChart C V O dd) {J : Fin 2 → Type} [∀ g, Fintype (J g)] (q : PairData Y d J) :
    (Y.raw q).hRow = (Y.k : C) • hAt Y ((Y.raw q).expPt 0) ((Y.raw q).expPt 1) := by
  unfold RawChart.hRow hAt
  congr 2
  funext x
  obtain ⟨g, i⟩ := x
  fin_cases g <;> rfl
end Formalism.L2.FormalSeriesBounds.VP
