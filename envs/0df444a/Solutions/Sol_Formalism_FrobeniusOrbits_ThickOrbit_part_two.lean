-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.ThickOrbit.part_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:56.24818+00:00
-- url     : https://prove2.me/submissions/ab15ad7c-7ad9-4436-b799-8b0822994850

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_int_mul_lt_of_le_four_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.ThickOrbit
namespace Formalism.FrobeniusOrbits.ThickOrbit
theorem _root_.solution {n L : ℕ} (hn : 0 < n) (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < n)
    (u₀ t h : ZMod n) (hord : addOrderOf h ≤ 4 * L) :
    {x : ZMod n | (∃ i : ℤ, x = t + i • h) ∧ InTranslate T u₀ x}.ncard ≤ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  rw [Set.ncard_le_one]
  rintro x ⟨⟨i, rfl⟩, s₁, hs₁, e₁⟩ y ⟨⟨i', rfl⟩, s₂, hs₂, e₂⟩
  set m := addOrderOf h with hm
  have hmpos : 0 < m := addOrderOf_pos h
  have hmh : (m : ZMod n) * h = 0 := by
    have := addOrderOf_nsmul_eq_zero h
    rwa [nsmul_eq_mul] at this
  rw [zsmul_eq_mul] at e₁ e₂
  set X : ℤ := (m : ℤ) * ((s₁ : ℤ) - s₂) with hX
  have hX0 : (X : ZMod n) = 0 := by
    rw [hX]; push_cast
    linear_combination (↑m : ZMod n) * (e₂ - e₁) + ((↑i : ZMod n) - ↑i') * hmh
  have hdvd : (n : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X n).mp hX0
  have h1 := int_mul_lt_of_le_four_mul (m : ℤ) s₁ (by exact_mod_cast hord) (hT s₁ hs₁)
  have h2 := int_mul_lt_of_le_four_mul (m : ℤ) s₂ (by exact_mod_cast hord) (hT s₂ hs₂)
  have p1 : 0 ≤ (m : ℤ) * (s₁ : ℤ) := by positivity
  have p2 : 0 ≤ (m : ℤ) * (s₂ : ℤ) := by positivity
  have habs : |X| < n := by
    rw [abs_lt, hX]
    constructor <;> nlinarith
  have hXz : X = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have hs : (s₁ : ℤ) = s₂ := by
    rw [hX] at hXz
    rcases mul_eq_zero.mp hXz with h0 | h0
    · omega
    · linarith
  have hs' : s₁ = s₂ := by exact_mod_cast hs
  subst hs'
  rw [zsmul_eq_mul, zsmul_eq_mul, e₁, e₂]
end Formalism.FrobeniusOrbits.ThickOrbit
