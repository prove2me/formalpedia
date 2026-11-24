-- Prove2me | solution 1 for CCRuleCW.leib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:08.472894+00:00
-- url     : https://prove2.me/submissions/4596a2b6-aa52-45a2-8c4e-bae7cd80236f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Theorems.Thm_CCRuleCW_apO_nil
import Theorems.Thm_CCRuleCW_apO_cons
import Theorems.Thm_CCRuleCW_LieW_head
import Theorems.Thm_CCRuleCW_LieW_tail
import Theorems.Thm_CCRuleCW_apO_local
import Theorems.Thm_CCRuleCW_apO_add
import Theorems.Thm_CCRuleCW_act_ck
import Theorems.Thm_CCRuleCW_act_leib
import Theorems.Thm_CCRuleCW_act_smooth_contDiff
import Theorems.Thm_CCRuleCW_smul_ck

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CCRuleCW.apO_nil
attribute [local simp] CCRuleCW.apO_cons

set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace CCRuleCW
theorem _root_.solution : ∀ (ops : List (Bool × B.Mat k r)), LieW ops → ∀ (Q : B.Mat k r → ℂ), ContDiff ℝ ∞ Q →
    ∀ (H : B.Mat k r → E), B.CkOn (⊤ : ℕ∞) (B.GV k r) H → ∀ g ∈ B.GV k r,
    apO ops (fun x => Q x • H x) g = ((splits ops).map (fun p => apO p.1 Q g • apO p.2 H g)).sum
  | [], _, Q, _, H, _, g, _ => by simp [splits]
  | o :: os, hl, Q, hQ, H, hH, g, hg => by
      simp only [apO_cons]
      rw [apO_local os hl.tail _ (fun x => act o Q x • H x + Q x • act o H x)
        (fun g' hg' => act_leib o hl.head Q hQ H hH g' hg') g hg]
      rw [apO_add os hl.tail _ _ (smul_ck _ (act_smooth_contDiff Q hQ o) H hH)
        (smul_ck Q hQ _ (act_ck H hH o hl.head)) g hg]
      rw [solution os hl.tail (act o Q) (act_smooth_contDiff Q hQ o) H hH g hg,
        solution os hl.tail Q hQ (act o H) (act_ck H hH o hl.head) g hg]
      simp [splits, List.map_append, List.sum_append, List.map_map, Function.comp_def]
end CCRuleCW
