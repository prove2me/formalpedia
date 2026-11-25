-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.blkAdm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:13.299872+00:00
-- url     : https://prove2.me/submissions/82e6c543-02be-4d40-ae0a-73cc8504972e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_attainsOK_of
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_le_sum_map
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
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (hdich : ∀ o ∈ Z, (X o).Alt ∨ ∀ a, (X o).big 0 a) (hj : ∀ o ∈ Z, (X o).j' < (X o).n)
    (hga : ∀ o ∈ Z, ∀ g a k, ga o g a k ≠ 0 → k ≤ (X o).rkF g a) : BlockAdmissible X F Z ga := by
  intro L hwt o ho q hq hatt
  refine attainsOK_of _ _ (hdich o ho) (hj o ho) q.1 q.2 (fun g a k hk => hga o ho g a k ?_) hatt
  rw [← hwt o ho g a k]
  have := le_sum_map (L o) (fun q => q.1.wt (X o) g a k) hq
  omega
end Formalism.L2.FormalSeriesBounds.RF
