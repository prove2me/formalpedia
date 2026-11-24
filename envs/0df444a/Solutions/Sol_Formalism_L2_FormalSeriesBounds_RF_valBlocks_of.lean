-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.valBlocks_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:43:08.960686+00:00
-- url     : https://prove2.me/submissions/22a5eb8c-fbbe-43f4-b211-fcf752280cf1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_valO_of
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_valBlocks_G


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
theorem _root_.solution (ν : ℝ) (hν : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x) (hs : PairsSep Y p)
    (hv : ValEqPSt Y p H Ls n) (hJ : JetProdSt) (hM : BlockMembershipChart Y p H Ls n F Z ga) (hA : BlockAdmissibleChart Y p H F Z ga) :
    ValBlocks (fun o => rd Y p H o) F Z n ga ν :=
  valBlocks_G (valO_of Y p H Ls n ν hν hs hv) hJ F Z ga hM hA
end Formalism.L2.FormalSeriesBounds.RF
