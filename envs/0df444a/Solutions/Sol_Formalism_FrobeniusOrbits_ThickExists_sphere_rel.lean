-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.ThickExists.sphere_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:32.106847+00:00
-- url     : https://prove2.me/submissions/6413987f-7c14-41b6-81ae-1180df5203f1

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.ThickExists
namespace Formalism.FrobeniusOrbits.ThickExists
theorem _root_.solution {S : ℕ} (v₁ v₂ v₃ : Fin S → ℤ) (k : ℤ) (h₁ : ∑ m, v₁ m ^ 2 = k)
    (h₂ : ∑ m, v₂ m ^ 2 = k) (h₃ : ∑ m, v₃ m ^ 2 = k) (i j : ℤ) (hj : j ≠ 0) (hij : i ≠ j)
    (h : ∀ m, j * (v₂ m - v₁ m) = i * (v₃ m - v₁ m)) : v₂ = v₁ := by
  have hA : ∑ m, (2 * v₁ m * (v₂ m - v₁ m) + (v₂ m - v₁ m) ^ 2) = 0 := by
    have e : ∀ m, 2 * v₁ m * (v₂ m - v₁ m) + (v₂ m - v₁ m) ^ 2 = v₂ m ^ 2 - v₁ m ^ 2 :=
      fun m => by ring
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, h₂, h₁, sub_self]
  have hB : ∑ m, (2 * v₁ m * (v₃ m - v₁ m) + (v₃ m - v₁ m) ^ 2) = 0 := by
    have e : ∀ m, 2 * v₁ m * (v₃ m - v₁ m) + (v₃ m - v₁ m) ^ 2 = v₃ m ^ 2 - v₁ m ^ 2 :=
      fun m => by ring
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, h₃, h₁, sub_self]
  have hW : ∑ m, i * (i - j) * (v₃ m - v₁ m) ^ 2 = 0 := by
    have e : ∀ m, i * (i - j) * (v₃ m - v₁ m) ^ 2
        = j ^ 2 * (2 * v₁ m * (v₂ m - v₁ m) + (v₂ m - v₁ m) ^ 2)
          - i * j * (2 * v₁ m * (v₃ m - v₁ m) + (v₃ m - v₁ m) ^ 2) := fun m => by
      linear_combination (-(2 * j * v₁ m + j * (v₂ m - v₁ m) + i * (v₃ m - v₁ m))) * h m
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hA, hB, mul_zero, mul_zero, sub_zero]
  by_cases hi : i = 0
  · funext m
    have h' := h m
    rw [hi, zero_mul] at h'
    have h'' := (mul_eq_zero.mp h').resolve_left hj
    linarith
  · have hne : i * (i - j) ≠ 0 := mul_ne_zero hi (sub_ne_zero.mpr hij)
    rw [← Finset.mul_sum] at hW
    have hs0 := (mul_eq_zero.mp hW).resolve_left hne
    have hw0 : ∀ m, v₃ m - v₁ m = 0 := by
      intro m
      have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => sq_nonneg (v₃ m - v₁ m))).mp hs0 m
        (Finset.mem_univ m)
      exact (pow_eq_zero_iff two_ne_zero).mp h'
    funext m
    have h' := h m
    rw [hw0 m, mul_zero] at h'
    have h'' := (mul_eq_zero.mp h').resolve_left hj
    linarith
end Formalism.FrobeniusOrbits.ThickExists
