-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.pullback_two_var_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:31:52.750275+00:00
-- url     : https://prove2.me/submissions/a8a3471f-fffb-4180-85a2-c717b1b119ff

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_linPull_mul


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
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
open Formalism.L2.FormalSeriesBounds.VP
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (F G : PS C 2 dd) : pull2 Y p (F * G) = pull2 Y p F * pull2 Y p G := by
  unfold pull2
  exact linPull_mul _ _ F G
end Formalism.L2.FormalSeriesBounds.VP
