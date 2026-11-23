-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.E2.middleThird_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:55.331723+00:00
-- url     : https://prove2.me/submissions/d41f51e8-9cf8-44de-8118-0e9b5cf9f009

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MiddleThirdEstimate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.E2
open Formalism.FourierDecayAlt.E Real Polynomial MeasureTheory
namespace Formalism.FourierDecayAlt.P.E2
theorem _root_.solution : MiddleThird := by
  intro n lam α β Y hI hroot hY1 hY2
  have hL : 0 < β - α := by linarith
  have key : ∀ s, (β-α)/3 ≤ |Y + lam s| := by
    intro s
    have h := hroot s
    simp only [Set.mem_Ioo, not_and_or, not_lt] at h
    rcases h with h | h
    · rw [le_abs]; left; linarith
    · rw [le_abs]; right; linarith
  have key2 : ∀ s, (β-α)/4 ≤ |Y + 1 + lam s| := by
    intro s
    have h := hroot s
    simp only [Set.mem_Ioo, not_and_or, not_lt] at h
    rcases h with h | h
    · rw [le_abs]; left; linarith
    · rw [le_abs]; right; linarith
  constructor
  · rw [← Finset.prod_div_distrib, Finset.abs_prod]
    calc ∏ s, |(Y + 1 + lam s) / (Y + lam s)| ≤ ∏ _s : Fin n, Real.exp (3 / (β - α)) := by
          apply Finset.prod_le_prod (fun s _ => abs_nonneg _)
          intro s _
          have h1 := key s
          have hpos : 0 < |Y + lam s| := by linarith
          have hne : Y + lam s ≠ 0 := abs_pos.mp hpos
          have e0 : (Y + 1 + lam s) / (Y + lam s) = 1 + 1 / (Y + lam s) := by field_simp; ring
          rw [e0]
          calc |1 + 1 / (Y + lam s)| ≤ 1 + 1/|Y + lam s| := by
                 have := abs_add_le (1:ℝ) (1 / (Y + lam s))
                 rw [abs_one, abs_div, abs_one] at this; exact this
            _ ≤ 1 + 3/(β-α) := by
                 have h2 : 1/|Y + lam s| ≤ 1/((β-α)/3) := one_div_le_one_div_of_le (by linarith) h1
                 have e : 1/((β-α)/3) = 3/(β-α) := by field_simp
                 linarith
            _ ≤ Real.exp (3/(β-α)) := by linarith [Real.add_one_le_exp (3/(β-α))]
      _ = Real.exp (3 * n / (β - α)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; congr 1; ring
  · rw [← Finset.prod_div_distrib, Finset.abs_prod]
    calc ∏ s, |(Y + lam s) / (Y + 1 + lam s)| ≤ ∏ _s : Fin n, Real.exp (4 / (β - α)) := by
          apply Finset.prod_le_prod (fun s _ => abs_nonneg _)
          intro s _
          have h1 := key2 s
          have hpos : 0 < |Y + 1 + lam s| := by linarith
          have hne : Y + 1 + lam s ≠ 0 := abs_pos.mp hpos
          have e0 : (Y + lam s) / (Y + 1 + lam s) = 1 + (-1) / (Y + 1 + lam s) := by field_simp; ring
          rw [e0]
          calc |1 + (-1) / (Y + 1 + lam s)| ≤ 1 + 1/|Y + 1 + lam s| := by
                 have := abs_add_le (1:ℝ) ((-1) / (Y + 1 + lam s))
                 rw [abs_one, abs_div, abs_neg, abs_one] at this; exact this
            _ ≤ 1 + 4/(β-α) := by
                 have h2 : 1/|Y + 1 + lam s| ≤ 1/((β-α)/4) := one_div_le_one_div_of_le (by linarith) h1
                 have e : 1/((β-α)/4) = 4/(β-α) := by field_simp
                 linarith
            _ ≤ Real.exp (4/(β-α)) := by linarith [Real.add_one_le_exp (4/(β-α))]
      _ = Real.exp (4 * n / (β - α)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; congr 1; ring
end Formalism.FourierDecayAlt.P.E2
