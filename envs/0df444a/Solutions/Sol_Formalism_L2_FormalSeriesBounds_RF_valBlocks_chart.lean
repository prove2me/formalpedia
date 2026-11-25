-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.valBlocks_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:11:24.28997+00:00
-- url     : https://prove2.me/submissions/052a44c5-f213-4e9b-b903-80a5d571cd30

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksChart
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_valBlocks_fin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_lower_of_nuPlE
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_valO_of


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
open Formalism.IncomingBounds
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
  (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
  (F : ∀ o, Flag (rd Y p H o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : PairsSep Y p) (hv : ValEqPSt Y p H Ls n)
    (hM : BlockMembershipChart Y p H Ls n F Z ga)
    (hdich : ∀ o ∈ Z, (rd Y p H o).Alt ∨ ∀ a, (rd Y p H o).big 0 a) (hj : ∀ o ∈ Z, (rd Y p H o).j' < (rd Y p H o).n)
    (hga : ∀ o ∈ Z, ∀ g a k, ga o g a k ≠ 0 → k ≤ (rd Y p H o).rkF g a) :
    ValBlocks (fun o => rd Y p H o) F Z n ga ν :=
  valBlocks_fin (valO_of Y p H Ls n ν (lower_of_nuPlE Y Ls n ν hν) hs hv) F Z ga hM hdich hj hga
end Formalism.L2.FormalSeriesBounds.RF
