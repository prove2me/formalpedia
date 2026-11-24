-- Prove2me | solution 1 for Formalism.IncomingBounds.baseTerm_le_topTerm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:57.384968+00:00
-- url     : https://prove2.me/submissions/8595db3e-e36a-4f82-8a40-2371862387fd

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_BaseTermLeTopTerm
import Theorems.Thm_Formalism_IncomingBounds_cor_tsum_cmp

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
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution (l d : ℕ) [NeZero d] (hl : 3 ≤ l) (TT : Finset (ZMod d))
    (nu1 nu2 : ZMod d → ℕ) (s : ZMod d) :
    baseTerm l d TT nu1 nu2 s ≤ topTerm l d TT nu1 nu2 s := by
  classical
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hb : Summable (fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) := by
    have : Summable (fun e : ℕ => ((l:ℝ)⁻¹) ^ e) :=
      summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
    simpa [div_eq_mul_inv, inv_pow] using this.mul_left (nu1 s : ℝ)
  unfold topTerm baseTerm
  refine cor_tsum_cmp (b := fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) ?_ ?_ ?_ hb
  · intro e
    try dsimp only
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  · intro e
    try dsimp only
    have hcap : (0:ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d)) := Nat.cast_nonneg _
    have hpe : (0:ℝ) < (l:ℝ) ^ e := pow_pos hl0 e
    have hn2 : (0:ℝ) ≤ (nu2 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    have hA' : (0:ℝ) ≤ (nu1 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    have hsub : ((nu1 s : ℝ) - nu2 s) / (l:ℝ) ^ e =
        (nu1 s : ℝ) / (l:ℝ) ^ e - (nu2 s : ℝ) / (l:ℝ) ^ e := sub_div _ _ _
    by_cases ho : Odd e
    swap
    · simp [ho]
    rcases lt_trichotomy (e : ℕ∞) (dTop d TT s) with hlt | heq | hgt
    · rw [if_pos (show Odd e ∧ (e : ℕ∞) < dTop d TT s from ⟨ho, hlt⟩)]
      split_ifs
      · apply max_le_max _ le_rfl
        rw [hsub]; linarith
      · exact le_max_right _ _
    · have hP : ∃ e0 : ℕ, dTop d TT s = (e0 : ℕ∞) ∧ s + (e : ZMod d) = s + (e0 : ZMod d) :=
        ⟨e, heq.symm, rfl⟩
      rw [if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => (lt_irrefl _ (heq ▸ h.2))),
        if_neg (show ¬ (Odd e ∧ dTop d TT s < (e : ℕ∞)) from fun h => (lt_irrefl _ (heq ▸ h.2)))]
      split_ifs with h
      · exact absurd hP h.2
      · exact le_rfl
    · rw [if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => (not_lt.mpr hgt.le h.2)),
        if_pos (show Odd e ∧ dTop d TT s < (e : ℕ∞) from ⟨ho, hgt⟩)]
      split_ifs
      · exact max_le (by rw [hsub]; linarith) hA'
      · exact hA'
  · intro e
    try dsimp only
    have hcap : (0:ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d)) := Nat.cast_nonneg _
    have hpe : (0:ℝ) < (l:ℝ) ^ e := pow_pos hl0 e
    have hA' : (0:ℝ) ≤ (nu1 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    split_ifs
    · exact max_le (by linarith) hA'
    · exact le_rfl
    · exact hA'
end Formalism.IncomingBounds
