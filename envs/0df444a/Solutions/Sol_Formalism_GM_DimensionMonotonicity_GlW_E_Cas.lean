-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.E_Cas
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:33.291972+00:00
-- url     : https://prove2.me/submissions/e49ab484-2be4-43fb-bb07-ead94dc4a800

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_apply
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity_GlW_comm__671fb396e97c
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
open Formalism.GM.DimensionMonotonicity.GlW
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.GM.DimensionMonotonicity.GlW
theorem _root_.solution (c d : Fin r) (x : V) : G.E c d (G.Cas x) = G.Cas (G.E c d x) := by
  have key : ∀ a b, G.E c d (G.E a b (G.E b a x)) = G.E a b (G.E b a (G.E c d x)) +
      (((if d = b then G.E a d (G.E c a x) else 0) - (if b = c then G.E a d (G.E c a x) else 0)) -
        ((if a = c then G.E c b (G.E b d x) else 0) - (if d = a then G.E c b (G.E b d x) else 0))) := by
    intro a b
    rw [G.comm' c d a b, G.comm' c d b a x, map_add, map_sub]
    split_ifs <;> subst_vars <;> (try simp only [map_zero]) <;> abel
  have h1 : ∀ a, ∑ b, ((if d = b then G.E a d (G.E c a x) else 0) - (if b = c then G.E a d (G.E c a x) else 0)) = 0 := by
    intro a
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  have h2 : ∑ a, ∑ b, ((if a = c then G.E c b (G.E b d x) else 0) - (if d = a then G.E c b (G.E b d x) else 0)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  calc G.E c d (G.Cas x) = ∑ a, ∑ b, G.E c d (G.E a b (G.E b a x)) := by
        rw [Cas_apply, map_sum]
        simp only [map_sum]
    _ = ∑ a, ∑ b, (G.E a b (G.E b a (G.E c d x)) +
        (((if d = b then G.E a d (G.E c a x) else 0) - (if b = c then G.E a d (G.E c a x) else 0)) -
          ((if a = c then G.E c b (G.E b d x) else 0) - (if d = a then G.E c b (G.E b d x) else 0)))) := by
        simp only [key]
    _ = G.Cas (G.E c d x) + (∑ a, ∑ b, ((if d = b then G.E a d (G.E c a x) else 0) - (if b = c then G.E a d (G.E c a x) else 0)) -
        ∑ a, ∑ b, ((if a = c then G.E c b (G.E b d x) else 0) - (if d = a then G.E c b (G.E b d x) else 0))) := by
        rw [Cas_apply]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = G.Cas (G.E c d x) := by
        rw [h2, Finset.sum_eq_zero (fun a _ => h1 a), sub_zero, add_zero]
end Formalism.GM.DimensionMonotonicity.GlW
