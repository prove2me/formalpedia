-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.pullback_one_var_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:35.897171+00:00
-- url     : https://prove2.me/submissions/da85186a-33eb-44db-9c44-8277431c2276

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_pull1Pt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_prod


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
theorem _root_.solution {ι : Type} (s : Finset ι) (F : ι → PS C 1 dd) :
    pull1 Y p (∏ i ∈ s, F i) = ∏ i ∈ s, pull1 Y p (F i) := by
  unfold pull1
  exact VP.subst_prod (cc_pull1Pt Y p) s F
end Formalism.L2.FormalSeriesBounds.VP
