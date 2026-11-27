-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.ge_pow_l_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:08:50.261927+00:00
-- url     : https://prove2.me/submissions/2817b9ba-e056-43b5-a6a1-10f3096a1395

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_ge_pow_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_ge_l
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_pow
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.GmExArith
theorem _root_.solution {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) {w ε : ℝ} (h : V.Ge w (A - B))
    (hε : ε ≤ 1) (hεw : ε ≤ w) : V.Ge (w + ε) (A ^ V.l - B ^ V.l) := by
  rw [← geom_sum₂_mul, show w + ε = ε + w from add_comm w ε]
  refine VF.Ge.mul ?_ h
  have e2 : ∀ i ∈ Finset.range V.l, B ^ i * B ^ (V.l - 1 - i) = B ^ (V.l - 1) := by
    intro i hi
    rw [← pow_add]; congr 1
    have := Finset.mem_range.1 hi; omega
  have e : ∑ i ∈ Finset.range V.l, A ^ i * B ^ (V.l - 1 - i) =
      ∑ i ∈ Finset.range V.l, (A ^ i - B ^ i) * B ^ (V.l - 1 - i) + (V.l : C) * B ^ (V.l - 1) := by
    rw [show (V.l : C) * B ^ (V.l - 1) = ∑ i ∈ Finset.range V.l, B ^ i * B ^ (V.l - 1 - i) by
      rw [Finset.sum_congr rfl e2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine VF.Ge.add (VF.Ge.sum fun i _ => ?_) ?_
  · rw [mul_comm]; exact (hB.pow _).mul_int ((ge_pow_sub hA hB h i).mono hεw)
  · rw [mul_comm]; exact (hB.pow _).mul_int ((VF.ge_l (V := V)).mono hε)
end Formalism.L2.FormalSeriesBounds.GmExArith
