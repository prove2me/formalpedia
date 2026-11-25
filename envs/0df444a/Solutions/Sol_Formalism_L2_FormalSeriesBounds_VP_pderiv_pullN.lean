-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.pderiv_pullN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:41:18.687805+00:00
-- url     : https://prove2.me/submissions/52e0f682-0c2c-4105-b223-be4d586e04c8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pderiv_rowOf
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_pullPt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_og
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
theorem _root_.solution {n : ℕ} (b : Fin n) (w : WVO I) (F : PS C n dd) :
    MvPowerSeries.pderiv C (b, w) (pullN Y p F) =
      ∑ j : Fin dd, rowOf b (MvPowerSeries.pderiv C w (expAll Y p j)) *
        pullN Y p (MvPowerSeries.pderiv C (b, j) F) := by
  unfold pullN
  rw [Formalism.L2.FormalSeriesBounds.pderiv_subst (Formalism.L2.FormalSeriesBounds.VP.og (fun q => cc_pullPt Y p q))]
  simp only [pderiv_rowOf]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp
  · intro a _ hab; simp [hab]
  · simp
end Formalism.L2.FormalSeriesBounds.VP
