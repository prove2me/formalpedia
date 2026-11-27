-- Prove2me | solution 1 for GRH.split_prime_lower_bound_at_squares_extends_to_mangoldt_majorant
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:45:30.117691+00:00
-- url     : https://prove2.me/submissions/0502d066-8e92-42a0-9263-dc7c17059dd5

import Definitions.Def_GRH_SplitPrimeLower
import Mathlib.Tactic.Linarith

open Finset ArithmeticFunction GRH.SplitPrimeLower

private theorem prime_le (q n : ℕ) : primeWeight q n ≤ mangoldtWeight q n := by
  apply sum_le_sum
  intro p hp
  by_cases h : p.Prime ∧ (p:ZMod q) = 1
  · simp [h,vonMangoldt.residueClass,Set.indicator_of_mem,vonMangoldt_apply_prime h.1]
  · simpa [h] using vonMangoldt.residueClass_nonneg (1:ZMod q) p

private theorem mono_weight (q : ℕ) : Monotone (mangoldtWeight q) := by
  intro m n h
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h)
  exact fun i _ _ => vonMangoldt.residueClass_nonneg (1:ZMod q) i

theorem solution (q : ℕ) (θ : ℝ) (hθ : (1/2:ℝ) ≤ θ) (h : squareLower q θ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 1 < x → 0 ≤ primeMajorant q D θ x := by
  obtain ⟨C,hC,hsq⟩ := h
  refine ⟨C*2^θ+3,by positivity,?_⟩
  intro x hx
  have hp : 0 < x := zero_lt_one.trans hx
  have ht : 0 ≤ θ := by linarith
  let u := (⌊x⌋₊).sqrt
  have hu : u^2 ≤ ⌊x⌋₊ := Nat.sqrt_le' _
  have hu' : (u:ℝ)^2 ≤ x := (show (u:ℝ)^2 ≤ (⌊x⌋₊:ℝ) by exact_mod_cast hu).trans (Nat.floor_le hp.le)
  have hgap : ⌊x⌋₊ ≤ u^2+2*u := by simpa [u,pow_two,two_mul,add_assoc] using Nat.sqrt_le_add ⌊x⌋₊
  have hgap' : (⌊x⌋₊:ℝ) ≤ (u:ℝ)^2+2*(u:ℝ) := by exact_mod_cast hgap
  have hs : (u:ℝ) ≤ x^θ := by
    calc
      _ ≤ Real.sqrt x := (Real.le_sqrt (by positivity) hp.le).mpr hu'
      _ ≤ _ := by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx.le hθ
  have hone : 1 ≤ x^θ := Real.one_le_rpow hx.le ht
  have hscale := Real.rpow_le_rpow (show 0 ≤ (u:ℝ)^2+1 by positivity)
    (show (u:ℝ)^2+1 ≤ 2*x by linarith) ht
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hp.le] at hscale
  have hweight := mul_le_mul_of_nonneg_left ((prime_le q _).trans (mono_weight q hu))
    (show (0:ℝ) ≤ q.totient by positivity)
  have hl := hsq u
  unfold primeMajorant
  nlinarith only [hl,hweight,mul_le_mul_of_nonneg_left hscale hC,hs,hone,hgap',Nat.lt_floor_add_one x]
