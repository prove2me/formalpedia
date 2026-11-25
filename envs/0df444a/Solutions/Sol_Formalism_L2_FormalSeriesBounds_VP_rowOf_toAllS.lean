-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.rowOf_toAllS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:26:54.858822+00:00
-- url     : https://prove2.me/submissions/c61c5f7d-16f2-40ba-bcd5-f45fb7e84cfe

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_rowOf_eq
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_rename
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rename_congr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_rowCopy_eq


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
theorem _root_.solution (b : Fin n) (o : Orb) (F : MvPowerSeries (WV (I o)) C) :
    rowOf b (toAllS o F) = MvPowerSeries.rename (eAll n o) (rowCopy b F) := by
  have e1 : toAllS o F =
      MvPowerSeries.rename (Function.Embedding.sigmaMk (β := fun o => WV (I o)) o) F := by
    unfold toAllS
    rw [MvPowerSeries.rename_eq_subst]
    rfl
  rw [rowOf_eq, e1, rtj_rowCopy_eq, MvPowerSeries.rename_rename, MvPowerSeries.rename_rename]
  exact rtj_rename_congr (by funext w; rfl) F
end Formalism.L2.FormalSeriesBounds.VP
