-- Prove2me | solution 1 for FunctionalInequalities.Analysis.legendre_norm_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:04.235995+00:00
-- url     : https://prove2.me/submissions/abf0266f-a987-472d-b094-e009ef1e7279

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_ne_bot_iff_readable

noncomputable section
section
open Set Filter
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Exact norm conjugate: zero on the closed unit ball and infinity outside. -/
theorem solution (y : E) :
    FunctionalInequalities.Analysis.legendre (fun x : E => (‖x‖ : EReal)) y = if ‖y‖ ≤ 1 then 0 else ⊤ := by
  by_cases hy : ‖y‖ ≤ 1
  · rw [if_pos hy]
    apply le_antisymm
    · apply iSup_le
      intro x
      rw [← EReal.coe_sub]
      apply EReal.coe_nonpos.mpr
      have h := (real_inner_le_norm x y).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg x))
      simpa only [mul_one] using sub_nonpos.mpr h
    · simpa only [FunctionalInequalities.Analysis.legendre, inner_zero_left, norm_zero, EReal.coe_zero, sub_zero] using
        (le_iSup (fun x : E => (inner ℝ x y : EReal) - (‖x‖ : EReal)) 0)
  · rw [if_neg hy]
    by_contra ht
    have hb := (FunctionalInequalities.Analysis.legendre_ne_bot_iff_readable (fun x : E => (‖x‖ : EReal)) y).mpr ⟨0, by simp⟩
    lift FunctionalInequalities.Analysis.legendre (fun x : E => (‖x‖ : EReal)) y to ℝ using ⟨ht, hb⟩ with r hr
    let d : ℝ := ‖y‖ ^ 2 - ‖y‖
    have hd : 0 < d := by dsimp [d]; nlinarith [lt_of_not_ge hy]
    let k : ℝ := (|r| + 1) / d
    have hk : 0 < k := div_pos (by positivity) hd
    have hterm : inner ℝ (k • y) y - ‖k • y‖ = |r| + 1 := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
      calc
        k * ‖y‖ ^ 2 - k * ‖y‖ = k * d := by dsimp [d]; ring
        _ = _ := div_mul_cancel₀ _ hd.ne'
    have h := le_iSup (fun x : E => (inner ℝ x y : EReal) - (‖x‖ : EReal)) (k • y)
    change (inner ℝ (k • y) y : EReal) - (‖k • y‖ : EReal) ≤
      FunctionalInequalities.Analysis.legendre (fun x : E => (‖x‖ : EReal)) y at h
    rw [← EReal.coe_sub, hterm, ← hr] at h
    have hreal := EReal.coe_le_coe_iff.mp h
    linarith [le_abs_self r]
