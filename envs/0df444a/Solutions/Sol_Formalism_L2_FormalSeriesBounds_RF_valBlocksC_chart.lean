-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.valBlocksC_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:20:52.806019+00:00
-- url     : https://prove2.me/submissions/9dcfdd37-a972-45e3-84cd-f9267506c6bb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksCChart
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_valO_self
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_blkAdmC
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_valBlocksC_G
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_jetProd


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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y 2 (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : SelfSep Y p) (hv : ValEqSelfSt Y p H Ls n)
    {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (F : ∀ o, Flag (rdS Y p H o)) (nW : ℕ) (hn : nW ≤ 2 * N + 1)
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (hM : BlockMembershipSelfConjugate (fun o => rdS Y p H o) N F (imgFamS Y p Ls n pl) gaC)
    (hA : ∀ o, (rdS Y p H o).Alt) (hj : ∀ o, (rdS Y p H o).j' < (rdS Y p H o).n)
    (hga : ∀ o s k, gaC o s k ≠ 0 → k ≤ (rdS Y p H o).rkF 0 s) :
    ValBlocksC (fun o => rdS Y p H o) F nW gaC ν :=
  valBlocksC_G (hV := valO_self (hν := hν) (hs := hs) (hv := hv) (pl := pl)) (hJ := jetProd) (F := F) (nW := nW)
    (hn := hn) (gaC := gaC) (hM := hM) (hA := blkAdmC (F := F) (gaC := gaC) (hA := hA) (hj := hj) (hga := hga))
end Formalism.L2.FormalSeriesBounds.RF
