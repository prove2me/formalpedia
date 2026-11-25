-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.valBlocks_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:20:53.975359+00:00
-- url     : https://prove2.me/submissions/b61d9096-d517-45b6-8e4f-c3d5d466b5db

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksChart
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_blkAdm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_valBlocks_G
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
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (I o) (J o)} {n : ℕ}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν)
    (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (hM : BlockMembership X n F FFimg Z ga)
    (hdich : ∀ o ∈ Z, (X o).Alt ∨ ∀ a, (X o).big 0 a) (hj : ∀ o ∈ Z, (X o).j' < (X o).n)
    (hga : ∀ o ∈ Z, ∀ g a k, ga o g a k ≠ 0 → k ≤ (X o).rkF g a) : ValBlocks X F Z n ga ν :=
  valBlocks_G hV jetProd F Z ga hM (blkAdm X F Z ga hdich hj hga)
end Formalism.L2.FormalSeriesBounds.RF
