-- Prove2me | solution 1 for Formalism.BehrendSets.E3.core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:15.260909+00:00
-- url     : https://prove2.me/submissions/d043d0d1-af22-4a45-80c6-0444e6854da1

import Definitions.Def_Formalism_BehrendSets_StatementE
import Mathlib
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_MulAbsSubLt
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_SpaceFreeOfBehrendFree
import Theorems.Thm_Formalism_BehrendSets_E3_idx_eq
import Theorems.Thm_Formalism_BehrendSets_Thick_mem_thick
import Theorems.Thm_Formalism_BehrendSets_Thick_mul_abs_sub_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Real
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.E3
namespace Formalism.BehrendSets.E3
theorem _root_.solution {n Lw : ℕ} [NeZero n] {S : Finset ℕ} (hS : ∀ s ∈ S, 4 * Lw * s < n)
    (hF : SpaceFreePos Lw S) {h u t : ZMod n} (hord : Lw < addOrderOf h) {i₁ i₂ i₃ : ℤ}
    (h12 : i₁ < i₂) (h23 : i₂ < i₃) (hw : i₃ - i₁ ≤ (Lw : ℤ))
    (m₁ : t + i₁ • h ∈ thick n S u) (m₂ : t + i₂ • h ∈ thick n S u)
    (m₃ : t + i₃ • h ∈ thick n S u) : False := by
  obtain ⟨y₁, hy₁, e₁⟩ := Thick.mem_thick.mp m₁
  obtain ⟨y₂, hy₂, e₂⟩ := Thick.mem_thick.mp m₂
  obtain ⟨y₃, hy₃, e₃⟩ := Thick.mem_thick.mp m₃
  set D : ℤ := (i₃ - i₁) * ((y₂ : ℤ) - y₁) - (i₂ - i₁) * ((y₃ : ℤ) - y₁) with hDdef
  have hZ : ((D : ℤ) : ZMod n) = 0 := by
    rw [hDdef]
    push_cast
    have e₁' := e₁
    have e₂' := e₂
    have e₃' := e₃
    rw [zsmul_eq_mul] at e₁' e₂' e₃'
    linear_combination ((i₂ : ZMod n) - i₃) * e₁' + ((i₃ : ZMod n) - i₁) * e₂'
      - ((i₂ : ZMod n) - i₁) * e₃'
  have hdvd : (n : ℤ) ∣ D := (ZMod.intCast_zmod_eq_zero_iff_dvd D n).mp hZ
  have bd : ∀ y ∈ S, (4 * (Lw : ℤ)) * (y : ℤ) < (n : ℤ) := by
    intro y hy
    have := hS y hy
    exact_mod_cast this
  have hL : (0 : ℤ) ≤ 4 * (Lw : ℤ) := by positivity
  have d₂ : 4 * (Lw : ℤ) * |(y₂ : ℤ) - y₁| < n :=
    Thick.mul_abs_sub_lt (by positivity) (by positivity) hL (bd y₂ hy₂) (bd y₁ hy₁)
  have d₃ : 4 * (Lw : ℤ) * |(y₃ : ℤ) - y₁| < n :=
    Thick.mul_abs_sub_lt (by positivity) (by positivity) hL (bd y₃ hy₃) (bd y₁ hy₁)
  have ha : |i₂ - i₁| ≤ (Lw : ℤ) := by rw [abs_le]; constructor <;> linarith
  have hb : |i₃ - i₁| ≤ (Lw : ℤ) := by rw [abs_le]; constructor <;> linarith
  have habsD : |D| ≤ |i₃ - i₁| * |(y₂ : ℤ) - y₁| + |i₂ - i₁| * |(y₃ : ℤ) - y₁| := by
    rw [hDdef, ← abs_mul, ← abs_mul]
    exact abs_sub _ _
  have k₁ : |i₃ - i₁| * |(y₂ : ℤ) - y₁| ≤ (Lw : ℤ) * |(y₂ : ℤ) - y₁| :=
    mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have k₂ : |i₂ - i₁| * |(y₃ : ℤ) - y₁| ≤ (Lw : ℤ) * |(y₃ : ℤ) - y₁| :=
    mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have hDlt : |D| < (n : ℤ) := by
    have q₁ : 4 * ((Lw : ℤ) * |(y₂ : ℤ) - y₁|) = 4 * (Lw : ℤ) * |(y₂ : ℤ) - y₁| := by ring
    have q₂ : 4 * ((Lw : ℤ) * |(y₃ : ℤ) - y₁|) = 4 * (Lw : ℤ) * |(y₃ : ℤ) - y₁| := by ring
    have : (0 : ℤ) ≤ |D| := abs_nonneg _
    linarith
  have hD0 : D = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hDlt
  by_cases c12 : y₁ = y₂
  · subst c12
    have := idx_eq hord (by rw [abs_sub_comm]; exact ha) e₁ e₂
    linarith
  by_cases c13 : y₁ = y₃
  · subst c13
    have := idx_eq hord (by rw [abs_sub_comm]; exact hb) e₁ e₃
    linarith
  by_cases c23 : y₂ = y₃
  · subst c23
    have h32 : |i₃ - i₂| ≤ (Lw : ℤ) := by rw [abs_le]; constructor <;> linarith
    have := idx_eq hord (by rw [abs_sub_comm]; exact h32) e₂ e₃
    linarith
  exact hF (i₂ - i₁) (i₃ - i₁) (by linarith) (by linarith) hw y₁ hy₁ y₂ hy₂ y₃ hy₃ c12 c13 c23
    (sub_eq_zero.mp hD0)
end Formalism.BehrendSets.E3
