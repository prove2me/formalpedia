-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.valBlocks_of_nuPlE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:19.815157+00:00
-- url     : https://prove2.me/submissions/fe0cfb92-4066-4e8f-8ee3-dc1171a1f931

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_lower_of_nuPlE
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_valBlocks_of

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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
  (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
variable (F : ∀ o, Flag (rd Y p H o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : PairsSep Y p)
    (hv : ValEqPSt Y p H Ls n) (hJ : JetProdSt) (hM : BlockMembershipChart Y p H Ls n F Z ga) (hA : BlockAdmissibleChart Y p H F Z ga) :
    ValBlocks (fun o => rd Y p H o) F Z n ga ν :=
  valBlocks_of Y p H Ls n F Z ga ν (lower_of_nuPlE Y Ls n ν hν) hs hv hJ hM hA
end Formalism.L2.FormalSeriesBounds.RF
