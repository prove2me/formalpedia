-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.gm_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:20:56.502395+00:00
-- url     : https://prove2.me/submissions/e819c3f4-1ac3-4033-8de6-8045e4721eeb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff

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
open Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable {d : ℕ} {I0 : Type} [Fintype I0]
namespace Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
theorem _root_.solution (Y : FBChart C V O dd) (p : SelfData Y d I0) (a : ZMod d) (r s : Fin 2) : V.Ge 0 (p.gm a r s) := by
  obtain ⟨M, hM⟩ := p.gm_lim 0
  have h1' := hM a r s
  simp only [Nat.cast_zero] at h1'
  have h1 : (0 : WithTop ℝ) ≤ V.v (p.gm a r s - p.em a (M r s)) := h1'
  have h2 : (0 : WithTop ℝ) ≤ V.v (p.em a (M r s)) := p.em_int a (M r s)
  show (0 : WithTop ℝ) ≤ V.v (p.gm a r s)
  have h3 := le_trans (le_min h1 h2) (AddValuation.map_add V.v _ _)
  rwa [sub_add_cancel] at h3
end Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
