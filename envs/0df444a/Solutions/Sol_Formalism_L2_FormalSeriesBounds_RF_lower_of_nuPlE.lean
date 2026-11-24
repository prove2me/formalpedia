-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.lower_of_nuPlE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:28:37.718112+00:00
-- url     : https://prove2.me/submissions/eff85ee6-2cb1-4337-aa97-7eba85c87941

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
  (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x := by
  intro x hx
  have h1 : (ν : EReal) ≤ (WithBot.some x : WithBot (WithTop ℝ)) := hν.trans (biInf_le _ hx)
  exact WithBot.coe_le_coe.1 h1
end Formalism.L2.FormalSeriesBounds.RF
