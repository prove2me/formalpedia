-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.ge_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:10:38.265943+00:00
-- url     : https://prove2.me/submissions/bc63831d-7e84-410d-854d-f08bd99aeed0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_int_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_not_mm_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_sum
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_GmExArith_ge_intCast__7e225cd13305
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1


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
theorem _root_.solution {z : C} (hz : IsIntegral ℤ z) : V.Ge 0 z := by
  by_contra hneg
  obtain ⟨p, hpm, hp⟩ := hz
  have hz0 : z ≠ 0 := by rintro rfl; exact hneg (VF.Ge.zero 0)
  have hw : V.MM z⁻¹ := by
    unfold VF.Ge at hneg; unfold VF.MM
    have e : V.v z + V.v z⁻¹ = 0 := by rw [← V.v.map_mul, mul_inv_cancel₀ hz0, V.v.map_one]
    induction ha : V.v z using WithTop.recTopCoe with
    | top => rw [ha] at hneg; exact absurd le_top hneg
    | coe r =>
      rw [ha] at hneg e
      have hr : r < 0 := by
        by_contra hr; exact hneg (by exact_mod_cast not_lt.1 hr)
      induction hb : V.v z⁻¹ using WithTop.recTopCoe with
      | top => exact WithTop.top_pos
      | coe s =>
        rw [hb] at e
        have e2 : r + s = 0 := by exact_mod_cast e
        exact_mod_cast (show (0 : ℝ) < s by linarith)
  have h0 : Polynomial.aeval z p = 0 := by rw [Polynomial.aeval_def]; exact hp
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, one_smul] at h0
  have hn : ∀ i ∈ Finset.range p.natDegree, V.MM ((p.coeff i • z ^ i) * z⁻¹ ^ p.natDegree) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have e : (p.coeff i • z ^ i) * z⁻¹ ^ p.natDegree = (p.coeff i : C) * z⁻¹ ^ (p.natDegree - i) := by
      rw [pow_sub₀ _ (inv_ne_zero hz0) hi'.le, ← inv_pow, inv_inv, zsmul_eq_mul]; ring
    rw [e]
    exact mm_int_mul (ge_intCast' _) (mm_pow hw (by omega))
  have e : (∑ i ∈ Finset.range p.natDegree, p.coeff i • z ^ i + z ^ p.natDegree) * z⁻¹ ^ p.natDegree
      = 0 * z⁻¹ ^ p.natDegree := by rw [h0]
  rw [add_mul, zero_mul, Finset.sum_mul, ← mul_pow, mul_inv_cancel₀ hz0, one_pow] at e
  have h1 : (1 : C) = -∑ i ∈ Finset.range p.natDegree, (p.coeff i • z ^ i) * z⁻¹ ^ p.natDegree := by
    linear_combination e
  have := mm_neg (mm_sum hn)
  rw [← h1] at this
  exact not_mm_one this
end Formalism.L2.FormalSeriesBounds.GmExArith
