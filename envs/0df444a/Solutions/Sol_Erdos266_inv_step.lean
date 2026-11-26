-- Prove2me | solution 1 for Erdos266.inv_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:04:50.718853+00:00
-- url     : https://prove2.me/submissions/e2e382f5-1253-4a8d-8467-befc43daf3fb

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
public import Theorems.Thm_Erdos266_blk_bound
public import Theorems.Thm_Erdos266_blk_close
public import Theorems.Thm_Erdos266_newQ_close
public import Theorems.Thm_Erdos266_stepSt_eq
public import Theorems.Thm_Erdos266_newS_eq_of_lt
public import Theorems.Thm_Erdos266_newS_eq_blk
public import Theorems.Thm_Erdos266_finSum_step
public import Theorems.Thm_Erdos266_bigN_pos
public import Theorems.Thm_Erdos266_dOf_succ_le
public import Theorems.Thm_Erdos266_mseq_cond
public import Theorems.Thm_Erdos266_mseq_dOf_le
public import Theorems.Thm_P2M_Erdos266__A_antitone_f8c2e918434c


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} {st : AlgSt} (h : Inv k st) : Inv (k + 1) (stepSt k st) := by
  rw [stepSt_eq h]
  have hk : 2 ≤ k := h.1
  have hd2 : dOf (k + 1) ≤ dOf k + 1 := dOf_succ_le k
  refine ⟨by omega, ?_, ?_⟩
  · -- the shift bounds
    intro l hl j hj
    by_cases hlk : l = k
    · subst hlk
      change |newS l st h l j| ≤ _
      rw [newS_eq_blk h hj]
      exact blk_bound h ⟨j, hj⟩
    · change |newS k st h l j| ≤ _
      rw [newS_eq_of_lt h hlk]
      exact h.2.1 l (by omega) j hj
  · -- the target estimates
    intro i hi
    change |finSum i (k+1) (newS k st h) + tailAnchor (i+1) (k+1)
        - (((if dOf (k + 1) = dOf k + 1
            then Function.update st.2 (dOf k) (newQ k st h)
            else st.2) i : ℚ) : ℝ)|
      ≤ εA (dOf (k+1)) * bigM (k+1) / (bigN (k+1) : ℝ) ^ (i + 2)
    have hNpos1 : (0:ℝ) < (bigN (k+1) : ℝ) ^ (i + 2) := by
      have := bigN_pos (k+1)
      positivity
    have hM1 : (0:ℝ) ≤ (bigM (k+1) : ℝ) := Nat.cast_nonneg _
    by_cases hcase : i < dOf k
    · -- a dimension that was already active
      have hx : (if dOf (k + 1) = dOf k + 1
            then Function.update st.2 (dOf k) (newQ k st h)
            else st.2) i = st.2 i := by
        split_ifs with hnew
        · exact Function.update_of_ne (by omega) _ _
        · rfl
      rw [hx, finSum_step h i]
      have hkey : finSum i k st.1 + (∑ j : Fin (dOf k),
            f (i + 1) ((((j.val + 1) * bigN k : ℕ) : ℝ) + (blk k st h j : ℝ)))
            + tailAnchor (i+1) (k+1) - (st.2 i : ℝ)
          = -(Xvec k st ⟨i, hcase⟩ - ∑ j : Fin (dOf k),
              f (i + 1) ((((j.val + 1) * bigN k : ℕ) : ℝ) + (blk k st h j : ℝ))) := by
        rw [Xvec]
        ring
      rw [hkey, abs_neg]
      refine (blk_close h ⟨i, hcase⟩).trans ?_
      -- the growth condition, then the antitone envelope
      obtain ⟨d', hd'⟩ : ∃ d', dOf k = d' + 1 := ⟨dOf k - 1, by omega⟩
      have hcond := mseq_cond d' k (by rw [← hd']; exact mseq_dOf_le hk) i (by omega)
      rw [show d' + 2 = dOf k + 1 from by omega, ← hd'] at hcond
      refine hcond.trans ?_
      have hεε : εA (dOf k + 1) ≤ εA (dOf (k + 1)) := εA_antitone hd2
      apply div_le_div_of_nonneg_right ?_ hNpos1.le
      exact mul_le_mul_of_nonneg_right hεε hM1
    · -- the newly entered dimension
      have hieq : i = dOf k := by omega
      have hnew : dOf (k + 1) = dOf k + 1 := by omega
      subst hieq
      rw [if_pos hnew, Function.update_self]
      exact (newQ_close h).le
end Erdos266
