-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_degree_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:11.408897+00:00
-- url     : https://prove2.me/submissions/6dbca3e1-4c40-4dd9-a721-38b449a72d90

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Theorems.Thm_Formalism_CountingSumsFrames_geom_sum_filter_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : SegDegreeSum := by
  intro p s P A C a ap b' i hp ha hap hP hPl hC hA
  have hpr : (2:ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((p:ℝ)^2)⁻¹ := ⟨_, rfl⟩
  have hp2 : (4:ℝ) ≤ (p:ℝ)^2 := by nlinarith
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq4 : q ≤ 1/4 := by
    calc q = ((p:ℝ)^2)⁻¹ := hq
      _ ≤ (4:ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      _ = 1/4 := by norm_num
  have hPi : 0 < (P i)⁻¹ := inv_pos.2 (hP i)
  have hb : 0 ≤ b' := by
    have := (le_div_iff₀ (by have := hP i; positivity : 0 < 2 * P i)).1 ((Nat.cast_nonneg (A i)).trans (hA i))
    linarith
  have hinv : ∀ l, l ≤ i → (P l)⁻¹ ≤ q ^ ((i:ℕ)-(l:ℕ)) * (P i)⁻¹ := by
    intro l hl
    rcases hl.lt_or_eq with h | h
    · have h' := hPl l h
      have e : q ^ ((i:ℕ)-(l:ℕ)) * (P i)⁻¹ = ((p:ℝ)^(2*((i:ℕ)-(l:ℕ))) * P i)⁻¹ := by
        rw [hq, inv_pow, ← pow_mul, mul_inv]
      rw [e]; exact inv_anti₀ (mul_pos (by positivity) (hP i)) h'
    · subst h; simp
  have hCs : (∑ l ∈ univ.filter (fun l => l < i), (C l:ℝ)) ≤
      2*a*(P i)⁻¹ * ∑ l ∈ univ.filter (fun l => l < i), q^((i:ℕ)-(l:ℕ)) := by
    rw [mul_sum]; apply sum_le_sum; intro l hl
    have hl' : l < i := (mem_filter.1 hl).2
    calc (C l:ℝ) ≤ ap / P l := hC l
      _ = ap * (P l)⁻¹ := div_eq_mul_inv _ _
      _ ≤ 2*a * (P l)⁻¹ := mul_le_mul_of_nonneg_right hap (inv_nonneg.2 (hP l).le)
      _ ≤ 2*a*(q^((i:ℕ)-(l:ℕ)) * (P i)⁻¹) := mul_le_mul_of_nonneg_left (hinv l hl'.le) (by linarith)
      _ = _ := by ring
  have hAs : (∑ l ∈ univ.filter (fun l => l ≤ i), (A l:ℝ)) ≤
      3/2*b'*(P i)⁻¹ * ∑ l ∈ univ.filter (fun l => l ≤ i), q^((i:ℕ)-(l:ℕ)) := by
    rw [mul_sum]; apply sum_le_sum; intro l hl
    have hl' : l ≤ i := (mem_filter.1 hl).2
    calc (A l:ℝ) ≤ 3 * b' / (2 * P l) := hA l
      _ = 3/2*b' * (P l)⁻¹ := by rw [div_eq_mul_inv, mul_inv]; ring
      _ ≤ 3/2*b'*(q^((i:ℕ)-(l:ℕ)) * (P i)⁻¹) := mul_le_mul_of_nonneg_left (hinv l hl') (by linarith)
      _ = _ := by ring
  have hins : univ.filter (fun l : Fin s => l ≤ i) = insert i (univ.filter (fun l => l < i)) := by
    ext l; simp [le_iff_eq_or_lt]
  have hsum : ∑ l ∈ univ.filter (fun l => l ≤ i), q^((i:ℕ)-(l:ℕ)) =
      1 + ∑ l ∈ univ.filter (fun l => l < i), q^((i:ℕ)-(l:ℕ)) := by
    rw [hins, sum_insert (by simp)]; simp
  have hg := (geom_sum_filter_le i q hq0).resolve_right (by linarith)
  rw [hsum] at hg hAs
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ l ∈ univ.filter (fun l => l < i), q^((i:ℕ)-(l:ℕ)) := ⟨_, rfl⟩
  rw [← hT] at hg hAs hCs
  have hT0 : 0 ≤ T := by rw [hT]; exact sum_nonneg (fun _ _ => by positivity)
  have hTq : T ≤ 4/3 * q := by nlinarith [mul_nonneg (sub_nonneg.2 hq4) hT0]
  have hT1 : 1 + T ≤ 4/3 := by linarith
  have hC2 : 2*a*(P i)⁻¹ * T ≤ 2*a*(P i)⁻¹ * (4/3*q) := mul_le_mul_of_nonneg_left hTq (by positivity)
  have hA2 : 3/2*b'*(P i)⁻¹ * (1+T) ≤ 3/2*b'*(P i)⁻¹ * (4/3) := mul_le_mul_of_nonneg_left hT1 (by positivity)
  have haq : 0 ≤ a * (P i)⁻¹ * q := by positivity
  rw [Int.le_floor]; push_cast; unfold SbdSeg
  have e : (4*a/(p:ℝ)^2+2*b')/P i = (4*a*q + 2*b')*(P i)⁻¹ := by rw [hq]; ring
  rw [e]
  nlinarith
end Formalism.CountingSumsFrames
