-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.error_sum_good_places
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:01.064797+00:00
-- url     : https://prove2.me/submissions/0d02f3d8-476c-497b-8ba4-8b63aa37b062

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.EigenvalueLevelCeiling
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : ErrSumGood := by
  classical
  intro PI hPI Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hPS
  obtain ⟨h1, h2, h3, h4, h5⟩ := hPS
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = PI.filter (fun p : ℕ => (p : ℝ) ≤ Y) := ⟨_, rfl⟩
  have hQp : ∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y := by
    intro p hp
    rw [hQ] at hp
    exact ⟨hPI p (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
  have e1 : ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p =
      ∑ p ∈ Q, 2 * (A1 * (Real.log (p : ℝ) / (p : ℝ)) + kw * (th p * Real.log (p : ℝ)) +
        T * (add p * Real.log (p : ℝ)) +
        A2 * (if X2 < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0) + Real.log (p : ℝ)) := by
    rw [hQ, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold errGood
    by_cases hp : (p : ℝ) ≤ Y
    · rw [if_pos hp, if_pos hp]
      by_cases hx : X2 < (p : ℝ)
      · rw [if_pos hx, if_pos hx]; ring
      · rw [if_neg hx, if_neg hx]; ring
    · rw [if_neg hp, if_neg hp]; ring
  have e2 : ∑ p ∈ Q, 2 * (A1 * (Real.log (p : ℝ) / (p : ℝ)) + kw * (th p * Real.log (p : ℝ)) +
        T * (add p * Real.log (p : ℝ)) +
        A2 * (if X2 < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0) + Real.log (p : ℝ)) =
      2 * (A1 * ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) + kw * ∑ p ∈ Q, th p * Real.log (p : ℝ) +
        T * ∑ p ∈ Q, add p * Real.log (p : ℝ) +
        A2 * ∑ p ∈ Q.filter (fun p : ℕ => X2 < (p : ℝ)), Real.log (p : ℝ) / (p : ℝ) ^ 2 +
        ∑ p ∈ Q, Real.log (p : ℝ)) := by
    rw [Finset.sum_filter, ← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [e1, e2]
  have b1 := mul_le_mul_of_nonneg_left (h1 Q hQp) hA1
  have b2 := mul_le_mul_of_nonneg_left (h4 Q (fun p hp => (hQp p hp).1)) hkw
  have b3 := h5 Q (fun p hp => (hQp p hp).1)
  have b4 := mul_le_mul_of_nonneg_left (h3 (Q.filter (fun p : ℕ => X2 < (p : ℝ)))
    (fun p hp => ⟨(hQp p (Finset.mem_filter.mp hp).1).1, (Finset.mem_filter.mp hp).2⟩)) hA2
  have b5 := h2 Q hQp
  have e3 : A2 * (2.04 / X2) = 2.04 * A2 / X2 := by ring
  linarith
end Formalism.EigenvalueLevelCeiling
