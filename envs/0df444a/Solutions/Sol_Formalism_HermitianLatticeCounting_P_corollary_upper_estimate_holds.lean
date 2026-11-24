-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.corollary_upper_estimate_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:04.899699+00:00
-- url     : https://prove2.me/submissions/0dfbc177-b343-4dbd-81ec-1653dbee878e

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_moment_ratio_telescoping

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
open scoped ENNReal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentUpwardHolder := by
  intro Ω _ μ _ r q l H0 R hm hpos hH0 hR h0 hc a
  have ha : a.val ≤ r := Nat.lt_succ_iff.1 a.isLt
  let M : ℕ → Ω → ℝ := fun i ω => if i = 0 then 1 else l ⟨min (i - 1) r, by omega⟩ ω
  let B : ℕ → ℝ := fun i => if i = 0 then H0 else R
  have hq : (a.val + 1) * q ≤ (r + 1) * q := Nat.mul_le_mul_right _ (by omega)
  have key := moment_ratio_telescoping μ M (a.val + 1) q B
    (by
      intro i
      by_cases hi : i = 0
      · simp only [M, hi, if_true]; exact measurable_const
      · simp only [M, hi, if_false]; exact hm _)
    (by
      intro i ω
      by_cases hi : i = 0
      · simp [M, hi]
      · simp only [M, hi, if_false]; exact hpos _ _)
    (by
      intro i
      by_cases hi : i = 0
      · simp [B, hi, hH0]
      · simp [B, hi, hR])
    (by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · have e0 : (⟨min (0 + 1 - 1) r, by omega⟩ : Fin (r + 1)) = 0 := Fin.ext (by simp)
        simp only [M, B, if_true, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, e0, div_one]
        exact h0 _ hq
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hk : k < r := by omega
        have e1 : (⟨min (k + 1 + 1 - 1) r, by omega⟩ : Fin (r + 1)) = (⟨k, hk⟩ : Fin r).succ :=
          Fin.ext (by simp; omega)
        have e2 : (⟨min (k + 1 - 1) r, by omega⟩ : Fin (r + 1)) = (⟨k, hk⟩ : Fin r).castSucc :=
          Fin.ext (by simp; omega)
        simp only [M, B, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, e1, e2]
        exact hc _ _ hq)
  have ea : (⟨min (a.val + 1 - 1) r, by omega⟩ : Fin (r + 1)) = a := Fin.ext (by simp; omega)
  simp only [M, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, if_true, ea, div_one] at key
  refine key.trans (le_of_eq ?_)
  congr 1
  rw [prod_range_succ']
  simp only [B, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, if_true, prod_const, card_range]
  rw [← pow_mul, mul_comm]
end Formalism.HermitianLatticeCounting.P
