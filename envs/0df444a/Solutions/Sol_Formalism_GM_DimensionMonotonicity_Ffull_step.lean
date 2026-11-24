-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.Ffull_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:07.166878+00:00
-- url     : https://prove2.me/submissions/07c565c7-d659-4073-a6dd-c43bcc42e7ad

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_takeD_update
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
import Theorems.Thm_Formalism_GM_extendSucc
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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (ρ : Fin r) (n : Fin T.t → ℕ) (n' : ℕ) (hn : n i ≤ n')
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) :
    T.Ffull p (LL.setTies T (Function.update n i n')) i ρ n' f =
      X (⟨T.pos i + 1, by have := hK_of_adm LL T hadm i; omega⟩, ρ) ^ (n' - n i) *
        T.Ffull p (LL.setTies T n) i ρ (n i) f := by
  have hK := hK_of_adm LL T hadm i
  rw [Ffull_eq, Ffull_eq, takeD_update LL T hadm i n n']
  set LLK := (LL.setTies T n).takeD (T.pos i + 1)
  have step : ∀ d : ℕ, freeze p LLK ρ (n i + d) f = X (Fin.last (T.pos i + 1), ρ) ^ d * freeze p LLK ρ (n i) f := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [← add_assoc, ← Formalism.GM.extendSucc p (T.pos i + 1) r LLK ρ (n i + d) (by omega) f, ih, pow_succ]
      ring
  rw [show n' = n i + (n' - n i) by omega, step, map_mul, map_pow, rename_X, Nat.add_sub_cancel_left]
  congr 2
  congr 1
  refine Prod.ext (Fin.ext ?_) rfl
  show ((ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) : Fin N) : ℕ) = T.pos i + 1
  rw [ιF_val hK]; simp
end Formalism.GM.DimensionMonotonicity
