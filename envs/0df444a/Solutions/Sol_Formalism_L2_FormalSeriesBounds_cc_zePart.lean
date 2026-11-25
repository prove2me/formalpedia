-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.cc_zePart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:47.188553+00:00
-- url     : https://prove2.me/submissions/412a8ef0-dba6-4c80-9b4a-4c922f170ca0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValueEquationOfProjectors

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
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (s : Orb × Fin 2) (m : Fin dd) :
    MvPowerSeries.constantCoeff (zePart Y p s m) = 0 := by
  unfold zePart
  simp
end Formalism.L2.FormalSeriesBounds
