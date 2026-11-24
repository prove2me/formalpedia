-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.sl2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:11.463855+00:00
-- url     : https://prove2.me/submissions/ed0f0422-5891-474e-8414-6775704a80e3

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_diag_of_isWt
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity_GlW_comm__671fb396e97c
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_isWt_pow
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
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.GM.DimensionMonotonicity.GlW
theorem _root_.solution {a b : Fin r} (hab : a ≠ b) {ν : Fin r → ℤ} {x : V} (hx : G.IsWt ν x) (k : ℕ) :
    G.E a b ((G.E b a ^ (k + 1)) x) = (G.E b a ^ (k + 1)) (G.E a b x) +
      (((k + 1 : ℕ) : K) * ((ν a - ν b - k : ℤ) : K)) • (G.E b a ^ k) x := by
  have hcomm : ∀ y, G.E a b (G.E b a y) = G.E b a (G.E a b y) + (G.E a a y - G.E b b y) := by
    intro y
    rw [G.comm' a b b a y, if_pos rfl, if_pos rfl]
  have hp : ∀ (j : ℕ) (y : V), G.E b a ((G.E b a ^ j) y) = (G.E b a ^ (j + 1)) y := by
    intro j y
    rw [pow_succ', Module.End.mul_apply]
  have hdiag : ∀ j : ℕ, G.E a a ((G.E b a ^ j) x) - G.E b b ((G.E b a ^ j) x) =
      ((ν a - ν b - 2 * (j : ℤ) : ℤ) : K) • (G.E b a ^ j) x := by
    intro j
    have hw := G.isWt_pow hx b a j
    rw [G.E_diag_of_isWt hw a, G.E_diag_of_isWt hw b, ← sub_smul]
    have e1 : (ν + (j : ℤ) • dl b a) a = ν a - j := by
      rw [Pi.add_apply, Pi.smul_apply, dl_apply, if_neg hab, if_pos rfl, smul_eq_mul]
      ring
    have e2 : (ν + (j : ℤ) • dl b a) b = ν b + j := by
      rw [Pi.add_apply, Pi.smul_apply, dl_apply, if_pos rfl, if_neg (Ne.symm hab), smul_eq_mul]
      ring
    rw [e1, e2]
    push_cast
    ring_nf
  induction k with
  | zero =>
    have h0 := hdiag 0
    simp only [pow_zero, Module.End.one_apply] at h0
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply]
    rw [hcomm, h0]
    congr 2
    push_cast
    ring
  | succ k ih =>
    rw [← hp (k + 1) x, ← hp (k + 1) (G.E a b x), hcomm, ih, hdiag (k + 1), map_add, map_smul, hp k x,
      add_assoc, ← add_smul]
    congr 2
    push_cast
    ring
end Formalism.GM.DimensionMonotonicity.GlW
