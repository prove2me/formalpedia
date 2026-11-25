-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.valBlocksC_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:24:14.563588+00:00
-- url     : https://prove2.me/submissions/e46e33b5-276a-4239-913f-4372127e6518

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksChart
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C}
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (I o) (J o)} {n : ℕ}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν)
    (F : ∀ o, Flag (X o)) (nW : ℕ) (hn : nW ≤ 2 * n + 1) (gaC : Orb → ZMod 2 → ℕ → ℕ) (hM : BlockMembershipSelfConjugate X n F FFimg gaC)
    (hA : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n) (hga : ∀ o s k, gaC o s k ≠ 0 → k ≤ (X o).rkF 0 s) :
    ValBlocksC X F nW gaC ν :=
  valBlocksC_G hV jetProd F nW hn gaC hM (blkAdmC X F gaC hA hj hga)
end Formalism.L2.FormalSeriesBounds.RF
