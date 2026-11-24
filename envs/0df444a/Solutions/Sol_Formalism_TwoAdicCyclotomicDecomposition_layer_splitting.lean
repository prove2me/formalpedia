-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layer_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:05.89907+00:00
-- url     : https://prove2.me/submissions/57cbbf89-2f69-4534-a650-8a0bd47d0b72

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {n q d : ℕ} {ζ a b : L}
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (h : IsLayer n q d ζ a b) :
    IsSplittingField ℚ L ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ))) := by
  obtain ⟨hζ, ha, hb, htop⟩ := h
  have hquad : ∀ (x : L) (c : ℕ), x ^ 2 = -(c : L) → Splits (X ^ 2 + C (c : L)) := by
    intro x c hx
    have : (X ^ 2 + C (c : L)) = (X - C x) * (X + C x) := by
      have hc : C (c : L) = - C (x ^ 2) := by rw [hx, C_neg, neg_neg]
      rw [hc, C_pow]; ring
    rw [this]; exact (Splits.X_sub_C x).mul (Splits.X_add_C x)
  have hne : ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)) : ℚ[X]) ≠ 0 :=
    (((monic_X_pow_sub_C 1 (pow_ne_zero _ two_ne_zero)).mul
      (monic_X_pow_add_C _ two_ne_zero)).mul (monic_X_pow_add_C _ two_ne_zero)).ne_zero
  constructor
  · have e : ((X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : ℚ)) * (X ^ 2 + C (d : ℚ)) : ℚ[X]).map
        (algebraMap ℚ L) = (X ^ (2 ^ n) - C 1) * (X ^ 2 + C (q : L)) * (X ^ 2 + C (d : L)) := by
      simp
    rw [e]
    exact ((X_pow_sub_one_splits hζ).mul (hquad a q ha)).mul (hquad b d hb)
  · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← htop,
      IntermediateField.adjoin_toSubalgebra]
    apply Algebra.adjoin_mono
    intro x hx
    rw [mem_rootSet]
    refine ⟨hne, ?_⟩
    rcases hx with rfl | rfl | rfl
    · simp [hζ.pow_eq_one]
    · simp [ha]
    · simp [hb]
end Formalism.TwoAdicCyclotomicDecomposition
