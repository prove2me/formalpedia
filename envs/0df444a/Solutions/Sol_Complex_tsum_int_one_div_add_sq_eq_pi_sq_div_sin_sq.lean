-- Prove2me | solution 1 for Complex.tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/629be84d-166a-5278-a3d5-d22d4b0a7126

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq

set_option autoImplicit false

open Complex Filter Metric
open scoped Real Topology

namespace EIS2K2

noncomputable def F (n : ℕ) (w : ℂ) : ℂ := 1 / (w - (n + 1)) + 1 / (w + (n + 1))

lemma sub_ne_zero_of_mem {w : ℂ} (hw : w ∈ integerComplement) (n : ℕ) : w - (n + 1) ≠ 0 := by
  have := integerComplement_add_ne_zero hw (-(n + 1 : ℤ))
  push_cast at this
  rwa [← sub_eq_add_neg] at this

lemma add_ne_zero_of_mem {w : ℂ} (hw : w ∈ integerComplement) (n : ℕ) : w + (n + 1) ≠ 0 := by
  have := integerComplement_add_ne_zero hw ((n + 1 : ℤ))
  push_cast at this
  exact this

lemma hasDerivAt_F {w : ℂ} (hw : w ∈ integerComplement) (n : ℕ) :
    HasDerivAt (F n) (-(1 / (w - (n + 1)) ^ 2) - 1 / (w + (n + 1)) ^ 2) w := by
  have h1 : HasDerivAt (fun w : ℂ => (w - (n + 1))⁻¹) (-(1 : ℂ) / (w - (n + 1)) ^ 2) w :=
    ((hasDerivAt_id w).sub_const _).inv (sub_ne_zero_of_mem hw n)
  have h2 : HasDerivAt (fun w : ℂ => (w + (n + 1))⁻¹) (-(1 : ℂ) / (w + (n + 1)) ^ 2) w :=
    ((hasDerivAt_id w).add_const _).inv (add_ne_zero_of_mem hw n)
  have h := h1.add h2
  have hF : F n = fun w : ℂ => (w - (n + 1))⁻¹ + (w + (n + 1))⁻¹ := by
    funext w; simp [F, one_div]
  rw [hF]
  convert h using 1
  · rfl
  · rfl
  · rfl
  simp only [one_div]
  ring

lemma differentiableOn_F {U : Set ℂ} (hU : U ⊆ integerComplement) (n : ℕ) : DifferentiableOn ℂ (F n) U :=
  fun _ hw => (hasDerivAt_F (hU hw) n).differentiableAt.differentiableWithinAt

lemma hasDerivAt_cot_sub {w : ℂ} (hw : w ∈ integerComplement) :
    HasDerivAt (fun x : ℂ => π * cot (π * x) - 1 / x)
      (-((π : ℂ) ^ 2 / Complex.sin (π * w) ^ 2) + 1 / w ^ 2) w := by
  have hs : Complex.sin (π * w) ≠ 0 := sin_pi_mul_ne_zero hw
  have hw0 : w ≠ 0 := integerComplement.ne_zero hw
  have hc : HasDerivAt (fun x : ℂ => Complex.cos (π * x)) (-Complex.sin (π * w) * π) w := by
    have := (Complex.hasDerivAt_cos (π * w)).comp w ((hasDerivAt_id w).const_mul (π : ℂ))
    simp at this ⊢
    exact this
  have hsd : HasDerivAt (fun x : ℂ => Complex.sin (π * x)) (Complex.cos (π * w) * π) w := by
    have := (Complex.hasDerivAt_sin (π * w)).comp w ((hasDerivAt_id w).const_mul (π : ℂ))
    simp at this
    exact this
  have hq := (hc.div hsd hs).const_mul (π : ℂ)
  have hi : HasDerivAt (fun x : ℂ => 1 / x) (-(1 : ℂ) / w ^ 2) w := by
    have := (hasDerivAt_id w).inv hw0
    simp [one_div] at this ⊢
    exact this
  have h := hq.sub hi
  have hfun : (fun x : ℂ => π * cot (π * x) - 1 / x)
      = fun x : ℂ => (π : ℂ) * (Complex.cos (π * x) / Complex.sin (π * x)) - 1 / x := by
    funext x; rw [Complex.cot_eq_cos_div_sin]
  rw [hfun]
  convert h using 1
  all_goals try rfl
  have hsc : Complex.sin (π * w) ^ 2 + Complex.cos (π * w) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
  have key : -Complex.sin (π * w) * π * Complex.sin (π * w) - Complex.cos (π * w) * (Complex.cos (π * w) * π)
      = -(π : ℂ) := by
    linear_combination (-(π : ℂ)) * hsc
  rw [key]
  field_simp
  ring

theorem hasSum_nat (z : ℂ) (hz : z ∈ integerComplement) :
    HasSum (fun n : ℕ => 1 / (z + (n + 1)) ^ 2 + 1 / (z - (n + 1)) ^ 2)
      ((π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2 - 1 / z ^ 2) := by

  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Complex.isOpen_compl_range_intCast z hz
  set r : ℝ := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  set U : Set ℂ := ball z r with hU
  have hUsub : U ⊆ integerComplement := fun w hw => hball (ball_subset_ball (by linarith) hw)
  have hdist : ∀ w ∈ U, ∀ m : ℤ, r ≤ ‖w - m‖ := by
    intro w hw m
    by_contra hlt
    push Not at hlt
    have hm : (m : ℂ) ∈ ball z ε := by
      rw [mem_ball, dist_comm]
      calc dist z m ≤ dist z w + dist w m := dist_triangle _ _ _
        _ < r + r := by
            gcongr
            · rw [dist_comm]; exact mem_ball.mp hw
            · rwa [dist_eq_norm]
        _ = ε := by rw [hr]; ring
    exact hball hm ⟨m, rfl⟩
  set R : ℝ := ‖z‖ + r with hR
  have hRpos : 0 < R := by positivity
  have hnormU : ∀ w ∈ U, ‖w‖ ≤ R := by
    intro w hw
    have : dist w z < r := mem_ball.mp hw
    rw [dist_eq_norm] at this
    calc ‖w‖ = ‖(w - z) + z‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ R := by rw [hR]; linarith

  set u : ℕ → ℝ := fun n => 8 * R * (((n : ℝ) + 1) ^ 2)⁻¹ + (if (n : ℝ) + 1 < 2 * R then 2 / r else 0) with hu
  have hu_sum : Summable u := by
    apply Summable.add
    · have h1 : Summable fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹ := by
        have := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)
        simpa using this
      exact h1.mul_left (8 * R)
    · apply summable_of_ne_finset_zero (s := Finset.range (Nat.ceil (2 * R)))
      intro n hn
      rw [Finset.mem_range, not_lt, Nat.ceil_le] at hn
      rw [if_neg]
      push Not
      linarith
  have hF_le : ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖F n w‖ ≤ u n := by
    intro n w hw
    have hw' := hUsub hw
    have h8 : 0 ≤ 8 * R * (((n : ℝ) + 1) ^ 2)⁻¹ := by positivity
    by_cases hn : (n : ℝ) + 1 < 2 * R
    ·
      simp only [hu, if_pos hn]
      have hb1 : ‖1 / (w - (n + 1))‖ ≤ 1 / r := by
        rw [norm_div, norm_one]
        have := hdist w hw (n + 1)
        push_cast at this
        exact one_div_le_one_div_of_le hr0 this
      have hb2 : ‖1 / (w + (n + 1))‖ ≤ 1 / r := by
        rw [norm_div, norm_one]
        have := hdist w hw (-(n + 1))
        push_cast at this
        rw [sub_neg_eq_add] at this
        exact one_div_le_one_div_of_le hr0 this
      calc ‖F n w‖ ≤ ‖1 / (w - (n + 1))‖ + ‖1 / (w + (n + 1))‖ := norm_add_le _ _
        _ ≤ 1 / r + 1 / r := add_le_add hb1 hb2
        _ = 2 / r := by ring
        _ ≤ _ := by linarith
    · push Not at hn
      simp only [hu, if_neg (not_lt.mpr hn), add_zero]
      have hwR := hnormU w hw
      have hm : ((n : ℝ) + 1) / 2 ≤ ‖w - (n + 1)‖ := by
        have : ‖((n : ℂ) + 1)‖ ≤ ‖w‖ + ‖w - (n + 1)‖ := by
          have := norm_sub_le w (w - (n + 1))
          rwa [show w - (w - ((n : ℂ) + 1)) = ((n : ℂ) + 1) by ring] at this
        have hn1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by norm_cast
        rw [hn1] at this
        linarith
      have hp : ((n : ℝ) + 1) / 2 ≤ ‖w + (n + 1)‖ := by
        have : ‖((n : ℂ) + 1)‖ ≤ ‖w + (n + 1)‖ + ‖w‖ := by
          have := norm_sub_le (w + (n + 1)) w
          rwa [show w + ((n : ℂ) + 1) - w = ((n : ℂ) + 1) by ring] at this
        have hn1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by norm_cast
        rw [hn1] at this
        linarith
      have hpos : 0 < ((n : ℝ) + 1) / 2 := by positivity
      have hFw : F n w = 2 * w / ((w - (n + 1)) * (w + (n + 1))) := by
        rw [F, div_add_div _ _ (sub_ne_zero_of_mem hw' n) (add_ne_zero_of_mem hw' n)]
        ring
      rw [hFw, norm_div, norm_mul, norm_mul, Complex.norm_two]
      have hden : (((n : ℝ) + 1) / 2) * (((n : ℝ) + 1) / 2) ≤ ‖w - (n + 1)‖ * ‖w + (n + 1)‖ :=
        mul_le_mul hm hp hpos.le (norm_nonneg _)
      have hdenpos : 0 < (((n : ℝ) + 1) / 2) * (((n : ℝ) + 1) / 2) := by positivity
      calc 2 * ‖w‖ / (‖w - (n + 1)‖ * ‖w + (n + 1)‖)
          ≤ 2 * R / ((((n : ℝ) + 1) / 2) * (((n : ℝ) + 1) / 2)) := by
            apply div_le_div₀ (by positivity) (by linarith) hdenpos hden
        _ = 8 * R * (((n : ℝ) + 1) ^ 2)⁻¹ := by
            field_simp
            ring

  have hzU : z ∈ U := mem_ball_self hr0
  have hderiv := Complex.hasSum_deriv_of_summable_norm hu_sum (differentiableOn_F hUsub) isOpen_ball hF_le hzU
  have hEq : (fun w : ℂ => ∑' n : ℕ, F n w) =ᶠ[𝓝 z] fun x : ℂ => π * cot (π * x) - 1 / x := by
    filter_upwards [isOpen_ball.mem_nhds hzU] with w hw
    rw [cot_series_rep' (hUsub hw)]
    rfl
  rw [hEq.deriv_eq, (hasDerivAt_cot_sub hz).deriv] at hderiv
  have hderiv' : HasSum (fun n : ℕ => -(1 / (z - (n + 1)) ^ 2) - 1 / (z + (n + 1)) ^ 2)
      (-((π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2) + 1 / z ^ 2) := by
    refine hderiv.congr_fun fun n => ?_
    exact ((hasDerivAt_F hz n).deriv).symm
  convert hderiv'.neg using 1
  all_goals try rfl
  · funext n; ring
  · ring

theorem main (z : ℂ) (hz : z ∈ integerComplement) :
    ∑' n : ℤ, 1 / (z + n) ^ 2 = (π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2 := by
  have hsum := hasSum_nat z hz
  set f : ℤ → ℂ := fun d => 1 / (z + d) ^ 2 with hf
  have hsZ : Summable f := by
    have h := EisensteinSeries.linear_right_summable z 1 (k := 2) (by norm_num)
    refine h.congr fun d => ?_
    simp only [hf, Int.cast_one, one_mul, one_div, zpow_ofNat]
  have hinjA : Function.Injective fun n : ℕ => (n : ℤ) + 1 := fun a b h => by
    simpa using h
  have hinjB : Function.Injective fun n : ℕ => -((n : ℤ) + 1) := fun a b h => by
    simpa using h
  have hA : Summable fun n : ℕ => f ((n : ℤ) + 1) := hsZ.comp_injective hinjA
  have hB : Summable fun n : ℕ => f (-((n : ℤ) + 1)) := hsZ.comp_injective hinjB
  have hA' : ∀ n : ℕ, f ((n : ℤ) + 1) = 1 / (z + (n + 1)) ^ 2 := fun n => by
    simp only [hf, Int.cast_add, Int.cast_natCast, Int.cast_one]
  have hB' : ∀ n : ℕ, f (-((n : ℤ) + 1)) = 1 / (z - (n + 1)) ^ 2 := fun n => by
    simp only [hf, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, sub_eq_add_neg]
  have hAB : (∑' n : ℕ, f ((n : ℤ) + 1)) + ∑' n : ℕ, f (-((n : ℤ) + 1))
      = (π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2 - 1 / z ^ 2 := by
    have h2 : HasSum (fun n : ℕ => f ((n : ℤ) + 1) + f (-((n : ℤ) + 1)))
        ((∑' n : ℕ, f ((n : ℤ) + 1)) + ∑' n : ℕ, f (-((n : ℤ) + 1))) := hA.hasSum.add hB.hasSum
    have h3 : HasSum (fun n : ℕ => f ((n : ℤ) + 1) + f (-((n : ℤ) + 1)))
        ((π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2 - 1 / z ^ 2) := by
      refine hsum.congr_fun fun n => ?_
      rw [hA', hB']
    exact h2.unique h3
  have htot : HasSum f ((∑' n : ℕ, f ((n : ℤ) + 1)) + f 0 + ∑' n : ℕ, f (-((n : ℤ) + 1))) :=
    hA.hasSum.of_add_one_of_neg_add_one hB.hasSum
  rw [htot.tsum_eq, add_right_comm, hAB]
  simp only [hf, Int.cast_zero, add_zero]
  ring

end EIS2K2

theorem solution (z : ℂ) (hz : z ∈ Complex.integerComplement) :
    ∑' n : ℤ, 1 / (z + n) ^ 2 = (π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2 :=
  EIS2K2.main z hz

end S_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq
end P2MW
export P2MW.S_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq (solution)
