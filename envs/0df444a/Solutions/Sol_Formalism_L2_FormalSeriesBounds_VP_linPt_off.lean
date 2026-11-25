-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.linPt_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:35.460816+00:00
-- url     : https://prove2.me/submissions/f3e8cdc2-d91a-4981-a731-8593d549f34d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_MS_off
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_linPt


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
theorem _root_.solution (b : Fin n) (hb : b ∉ Set.range pl) (i : Fin dd) : linPt Y (MS Y p pl) (b, i) = 0 := by
  have h0 : linS (colLin (MS Y p pl) b) = 0 := by
    funext j
    simp [linS, colLin, MS_off Y p pl _ b hb]
  have hc := cc_linPt Y (MS Y p pl) (b, i)
  simp only [linPt, h0, MvPowerSeries.subst_zero_eq_C_constantCoeff] at hc ⊢
  simp at hc
  simp [hc]
end Formalism.L2.FormalSeriesBounds.VP
