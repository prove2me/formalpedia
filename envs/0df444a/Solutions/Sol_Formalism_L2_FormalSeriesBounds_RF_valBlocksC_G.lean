-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.valBlocksC_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:28.30757+00:00
-- url     : https://prove2.me/submissions/27173543-3cac-47c5-a2a3-a0d0dd4e168a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_val_lists
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
  (X : ∀ o, RowData C V 2 (I o) (J o)) (n : ℕ)
variable {X n}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν) (hJ : JetProdSt)
    (F : ∀ o, Flag (X o)) (nW : ℕ) (hn : nW ≤ 2 * n + 1) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (hM : BlockMembershipSelfConjugate X n F FFimg gaC) (hA : BlockAdmissibleSelfConjugate X F gaC) : ValBlocksC X F nW gaC ν := by
  intro L hatt hmon hrows hwt
  exact val_lists hV hJ F L (fun o q hq => hA L hwt o q hq (hatt o q hq)) (by omega) (hM L hmon hwt)
end Formalism.L2.FormalSeriesBounds.RF
