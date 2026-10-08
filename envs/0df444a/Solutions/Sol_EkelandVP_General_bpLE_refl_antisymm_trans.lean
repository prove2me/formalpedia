-- Prove2me | solution 1 for EkelandVP.General.bpLE_refl_antisymm_trans
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T15:06:39.292123+00:00
-- url     : https://prove2.me/submissions/fe268df4-dc4b-43a9-ae52-7118bab889eb

import Mathlib
import Definitions.Def_EkelandVP_General_bpLE

set_option autoImplicit false

open EkelandVP.General in
theorem solution {V : Type*} [MetricSpace V] (α : ℝ) (hα : 0 < α) :
    (∀ p : V × ℝ, bpLE α p p) ∧
    (∀ p q : V × ℝ, bpLE α p q → bpLE α q p → p = q) ∧
    (∀ p q r : V × ℝ, bpLE α p q → bpLE α q r → bpLE α p r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    unfold bpLE
    simp
  · rintro ⟨v₁, a₁⟩ ⟨v₂, a₂⟩ h1 h2
    unfold bpLE at h1 h2
    simp only at h1 h2
    have hd : 0 ≤ dist v₁ v₂ := dist_nonneg
    have hs : dist v₂ v₁ = dist v₁ v₂ := dist_comm _ _
    rw [hs] at h2
    have hz : α * dist v₁ v₂ ≤ 0 := by linarith
    have hd0 : dist v₁ v₂ = 0 := by
      by_contra hne
      have : 0 < dist v₁ v₂ := lt_of_le_of_ne hd (Ne.symm hne)
      have := mul_pos hα this
      linarith
    have hv : v₁ = v₂ := dist_eq_zero.mp hd0
    have ha : a₁ = a₂ := by rw [hd0] at h1 h2; linarith
    rw [hv, ha]
  · rintro ⟨v₁, a₁⟩ ⟨v₂, a₂⟩ ⟨v₃, a₃⟩ h1 h2
    unfold bpLE at h1 h2 ⊢
    simp only at h1 h2 ⊢
    have ht : dist v₁ v₃ ≤ dist v₁ v₂ + dist v₂ v₃ := dist_triangle _ _ _
    have := mul_le_mul_of_nonneg_left ht hα.le
    nlinarith
