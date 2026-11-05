-- Prove2me | solution 1 for ChenFarias.SimplePolicy.max_horizon_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:47:41.824418+00:00
-- url     : https://prove2.me/submissions/bb9490a8-98a6-4061-bc72-07fa39da60c9

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model
import Theorems.Thm_ChenFarias_SimplePolicy_lemma_8

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open ChenFarias.SimplePolicy

lemma cf_J_mono (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 : ℕ)
    (hπ : ∀ x : ℕ, 1 ≤ x → 0 ≤ π x) {s T : ℝ} (hsT : s ≤ T) :
    J lam f π x0 s ≤ J lam f π x0 T := by
  unfold J
  refine lintegral_mono (fun e => ENNReal.ofReal_le_ofReal ?_)
  unfold revenueBy
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hk' := Finset.mem_Icc.1 hk
  have h0 : 0 ≤ π (x0 - k + 1) := hπ _ (by omega)
  split_ifs with h1 h2 <;> first | exact le_rfl | exact h0 | exact absurd (h1.trans hsT) h2

theorem solution (lam β T : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ)
    (π : ℕ → ℝ) (x0 : ℕ) (hlam : 0 < lam) (hβ : 0 < β)
    (hT : 0 < T) (hf : Assumption1 f) (hV : IsValueFn lam β f V)
    (hπ : IsRootPolicy f V π) :
    (∫⁻ s, J lam f π x0 s ∂expMeasure β) ≤
      (∫⁻ s, ENNReal.ofReal (max 1 (s / T)) ∂expMeasure β) *
        J lam f π x0 T := by
  have hπ0 : ∀ x : ℕ, 1 ≤ x → 0 ≤ π x := fun x hx => (hπ x hx).1
  have hmeas : Measurable (fun s : ℝ => ENNReal.ofReal (max 1 (s / T))) := by fun_prop
  rw [← lintegral_mul_const _ hmeas]
  refine lintegral_mono (fun s => ?_)
  rcases le_or_gt s T with hs | hs
  · calc J lam f π x0 s ≤ J lam f π x0 T := cf_J_mono lam f π x0 hπ0 hs
      _ = ENNReal.ofReal 1 * J lam f π x0 T := by simp
      _ ≤ ENNReal.ofReal (max 1 (s / T)) * J lam f π x0 T := by
          gcongr; exact le_max_left _ _
  · have h8 := lemma_8 lam β s T f V π x0 hlam hβ hT hs hf hV hπ
    have hs0 : 0 < s := hT.trans hs
    have hne : ENNReal.ofReal s ≠ 0 := by simp [hs0]
    have hTne : ENNReal.ofReal T ≠ 0 := by simp [hT]
    calc J lam f π x0 s = J lam f π x0 s / ENNReal.ofReal s * ENNReal.ofReal s :=
          (ENNReal.div_mul_cancel hne ENNReal.ofReal_ne_top).symm
      _ ≤ J lam f π x0 T / ENNReal.ofReal T * ENNReal.ofReal s := by gcongr
      _ = ENNReal.ofReal (s / T) * J lam f π x0 T := by
          rw [ENNReal.ofReal_div_of_pos hT, div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ ≤ ENNReal.ofReal (max 1 (s / T)) * J lam f π x0 T := by
          gcongr; exact le_max_right _ _
