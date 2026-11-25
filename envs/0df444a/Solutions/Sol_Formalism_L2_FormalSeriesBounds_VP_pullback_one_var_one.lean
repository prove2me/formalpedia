-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.pullback_one_var_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:40.858514+00:00
-- url     : https://prove2.me/submissions/3f7830bf-0093-4149-a89f-719f0fb65a78

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_pull1Pt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_one


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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution : pull1 Y p (1 : PS C 1 dd) = 1 := by
  unfold pull1
  exact VP.subst_one (cc_pull1Pt Y p)
end Formalism.L2.FormalSeriesBounds.VP
