-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.eq_one_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T06:12:38.159835+00:00
-- url     : https://prove2.me/submissions/4b3a9c61-2322-4741-b8de-cc142e0053b4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_ge
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_not_mm_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_pow_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.GmExArith
theorem _root_.solution {u : C} {N : ℕ} (hN : V.MM ((N : C) + 1)) (hu1 : u ^ N = 1) (hum : V.MM (u - 1)) : u = 1 := by
  have hui : V.Ge 0 u := by
    have : u = (u - 1) + 1 := by ring
    rw [this]; exact (mm_ge hum).add VF.Ge.one
  have hS : V.MM ((∑ i ∈ Finset.range N, u ^ i) + 1) := by
    have e : (∑ i ∈ Finset.range N, u ^ i) + 1 =
        (∑ i ∈ Finset.range N, (u ^ i - 1 ^ i)) + ((N : C) + 1) := by
      rw [Finset.sum_sub_distrib]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      ring
    rw [e]
    exact mm_add (mm_sum fun i _ => mm_pow_sub hui VF.Ge.one hum i) hN
  have hS0 : (∑ i ∈ Finset.range N, u ^ i) ≠ 0 := by
    intro h0; rw [h0, zero_add] at hS; exact not_mm_one hS
  have h3 : (∑ i ∈ Finset.range N, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu1, sub_self]
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hS0)
end Formalism.L2.FormalSeriesBounds.GmExArith
