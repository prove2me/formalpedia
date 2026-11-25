-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.toAllS_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:02:56.305783+00:00
-- url     : https://prove2.me/submissions/47c47d1c-5d8f-45f7-8b27-f3e2e2aa3b7f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_mul


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
variable {n : ℕ}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (o : Orb) (F G : MvPowerSeries (WV (I o)) C) : toAllS o (F * G) = toAllS o F * toAllS o G := by
  unfold toAllS
  exact VP.subst_mul (fun _ => MvPowerSeries.constantCoeff_X _) F G
end Formalism.L2.FormalSeriesBounds.VP
