-- Prove2me | solution 1 for Formalism.CountingSumsFrames.sum_update_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:11.381792+00:00
-- url     : https://prove2.me/submissions/feb4f976-f054-4cf6-b1b3-37e6991f5186

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds

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
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {s : ℕ} (As : Fin s → Finset ℕ) (i : Fin s) (g : (Fin s → ℕ) → ℝ) :
    ∑ aa ∈ Fintype.piFinset As, ∑ x ∈ As i, g (Function.update aa i x) =
      ((As i).card : ℝ) * ∑ aa ∈ Fintype.piFinset As, g aa := by
  have key : ∑ p ∈ Fintype.piFinset As ×ˢ As i, g (Function.update p.1 i p.2) =
      ∑ p ∈ Fintype.piFinset As ×ˢ As i, g p.1 := by
    apply Finset.sum_nbij' (fun p => (Function.update p.1 i p.2, p.1 i))
      (fun p => (Function.update p.1 i p.2, p.1 i))
    · rintro ⟨aa, x⟩ h
      simp only [Finset.mem_product, Fintype.mem_piFinset] at h ⊢
      refine ⟨fun j => ?_, h.1 i⟩
      rcases eq_or_ne j i with rfl | hj
      · simp [h.2]
      · simp [Function.update_of_ne hj, h.1 j]
    · rintro ⟨aa, x⟩ h
      simp only [Finset.mem_product, Fintype.mem_piFinset] at h ⊢
      refine ⟨fun j => ?_, h.1 i⟩
      rcases eq_or_ne j i with rfl | hj
      · simp [h.2]
      · simp [Function.update_of_ne hj, h.1 j]
    · rintro ⟨aa, x⟩ _
      simp
    · rintro ⟨aa, x⟩ _
      simp
    · rintro ⟨aa, x⟩ _
      rfl
  rw [← Finset.sum_product', key, Finset.sum_product]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.mul_sum]
end Formalism.CountingSumsFrames
