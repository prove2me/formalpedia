-- Prove2me | solution 1 for Formalism.IncomingBounds.top_radius_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:16.797792+00:00
-- url     : https://prove2.me/submissions/85011468-832f-4cd7-b181-ade660a13e4d

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_AltChooseSumEqZero

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
open Finset fwdDiff
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : TopRadius := by
  intro l hl A cap J hA hcap hJ
  set T := (Finset.range J).filter Odd with hT
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hlpos : (0 : ℝ) < l := by linarith
  have hpow : ∀ n : ℕ, (0 : ℝ) < (l : ℝ) ^ n := fun n => pow_pos hlpos n
  have hle1 : ∀ j k : ℕ, max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 ≤ 1 := by
    intro j k
    apply max_le _ zero_le_one
    have : 0 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹ := by positivity
    linarith
  let S := T.filter (fun j => A / (l : ℝ) ^ j ≤ cap j)
  by_cases hS : S.Nonempty
  · obtain ⟨k, hkS, hkmin⟩ : ∃ k ∈ S, ∀ j ∈ S, k ≤ j :=
      ⟨S.min' hS, S.min'_mem hS, fun j hj => S.min'_le j hj⟩
    have hkT : k ∈ T := (Finset.mem_filter.mp hkS).1
    have hkJ : k < J := Finset.mem_range.mp (Finset.mem_filter.mp hkT).1
    have hkcap : A / (l : ℝ) ^ k ≤ cap k := (Finset.mem_filter.mp hkS).2
    refine ⟨((l : ℝ) ^ k)⁻¹, ?_, ?_⟩
    · exact inv_anti₀ (hpow k) (pow_le_pow_right₀ hl1 hkJ.le)
    · have hterm : ∀ j ∈ T, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 +
          (if j = k then A * ((l : ℝ) ^ k)⁻¹ else 0) ≤ min (cap j) (A / (l : ℝ) ^ j) := by
        intro j hj
        rcases lt_trichotomy j k with hjk | hjk | hjk
        · have hjS : j ∉ S := fun h => absurd (hkmin j h) (by omega)
          have hlt : cap j < A / (l : ℝ) ^ j := by
            by_contra hc
            push Not at hc
            exact hjS (Finset.mem_filter.mpr ⟨hj, hc⟩)
          rw [if_neg (by omega), add_zero, min_eq_left hlt.le]
          calc cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 ≤ cap j * 1 :=
                mul_le_mul_of_nonneg_left (hle1 j k) (hcap j)
            _ = cap j := mul_one _
        · subst hjk
          rw [if_pos rfl, mul_inv_cancel₀ (hpow j).ne', sub_self, max_self, mul_zero, zero_add,
            min_eq_right hkcap, div_eq_mul_inv]
        · have h1 : 1 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ (hpow k), one_mul]
            exact pow_le_pow_right₀ hl1 hjk.le
          rw [if_neg (by omega), add_zero, max_eq_right (by linarith), mul_zero]
          exact le_min (hcap j) (div_nonneg hA (hpow j).le)
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hkT] at hsum
      have : 0 ≤ A / (l : ℝ) ^ J := div_nonneg hA (hpow J).le
      linarith
  · have hS' : ∀ j ∈ T, cap j < A / (l : ℝ) ^ j := by
      intro j hj
      by_contra hc
      push Not at hc
      exact hS ⟨j, Finset.mem_filter.mpr ⟨hj, hc⟩⟩
    refine ⟨((l : ℝ) ^ J)⁻¹, le_rfl, ?_⟩
    have hterm : ∀ j ∈ T, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ J)⁻¹) 0 ≤
        min (cap j) (A / (l : ℝ) ^ j) := by
      intro j hj
      rw [min_eq_left (hS' j hj).le]
      calc cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ J)⁻¹) 0 ≤ cap j * 1 :=
            mul_le_mul_of_nonneg_left (hle1 j J) (hcap j)
        _ = cap j := mul_one _
    have hsum := Finset.sum_le_sum hterm
    rw [div_eq_mul_inv A]
    linarith
end Formalism.IncomingBounds
