-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.linPt_pl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:00:05.157434+00:00
-- url     : https://prove2.me/submissions/6626f800-426e-4d61-94e5-6d0029b0cac6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_MS_pl
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_rowOf_eq
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rename_subst_linS


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
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (ρ : Fin N) (col : Fin 2) (i : Fin dd) :
    linPt Y (MS Y p pl) (pl (ρ, col), i) = rowOf ρ (linPt Y (uS Y p) (col, i)) := by
  simp only [linPt]
  rw [rowOf_eq, rename_subst_linS]
  congr 1
  funext j
  simp only [linS, colLin, map_sum, map_smul, MvPowerSeries.rename_X]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single ρ]
  · simp only [MS_pl, if_true]
    rfl
  · intro ρ' _ hρ'
    simp [MS_pl, hρ']
  · simp
end Formalism.L2.FormalSeriesBounds.VP
