-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.valO_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:52.340586+00:00
-- url     : https://prove2.me/submissions/48bd1d56-f657-48aa-bd71-3d9928149f05

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksCChart
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_val_self


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
variable {d : ℕ} [NeZero d] (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : SelfSep Y p) (hv : ValEqSelfSt Y p H Ls n)
    {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) : ValO (fun o => rdS Y p H o) N (imgFamS Y p Ls n pl) ν := by
  rintro Po ⟨P, hP, hQ⟩ kind hk S t ht gr hg
  have key := val_self (hs := hs) (hv := hv) (N := N) (pl := pl) (P := P) (hP := hP) (Po := Po) (hQ := hQ)
    (kind := kind) (hk := hk) (S := S) (t := t) (ht := ht) (gr := gr) (hg := hg)
  exact WithBot.coe_le_coe.1 (hν.trans key)
end Formalism.L2.FormalSeriesBounds.RF
