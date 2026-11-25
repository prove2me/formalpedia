-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.pderiv_rowOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:16:32.074655+00:00
-- url     : https://prove2.me/submissions/88c8940f-6e29-4311-8376-f42076fa4463

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_og
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_pderiv_subst


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
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {n : ℕ} (b b' : Fin n) (w : WVO I) (E : MvPowerSeries (WVO I) C) :
    MvPowerSeries.pderiv C (b, w) (rowOf b' E) = if b' = b then rowOf b (MvPowerSeries.pderiv C w E) else 0 := by
  unfold rowOf
  rw [Formalism.L2.FormalSeriesBounds.pderiv_subst (Formalism.L2.FormalSeriesBounds.VP.og (fun v => MvPowerSeries.constantCoeff_X _))]
  by_cases h : b' = b
  · subst h
    simp [MvPowerSeries.pderiv_X, Pi.single_apply, Prod.ext_iff]
  · simp [MvPowerSeries.pderiv_X, Pi.single_apply, Prod.ext_iff, h]
end Formalism.L2.FormalSeriesBounds.VP
