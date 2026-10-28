-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.eq_A_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:19:52.240505+00:00
-- url     : https://prove2.me/submissions/634a9555-777b-4b23-bb3a-a6fd1e4bd4e0

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

namespace Aux_BoundedEntropyGames_ConvRate_eq_A_9
open BoundedEntropyGames.ConvRate

theorem marginal {𝒳 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒜] [DecidableEq 𝒜]
    (pA : 𝒜 → ℝ) (hpA : IsPMF pA) (φ : 𝒜 → ℝ) (x : 𝒳) :
    ∑ f : 𝒳 → 𝒜, pF pA f * φ (f x) = ∑ b, pA b * φ b := by
  set h : 𝒳 → 𝒜 → ℝ := fun y b => pA b * (if y = x then φ b else 1) with hh
  have e1 : ∀ f : 𝒳 → 𝒜, pF pA f * φ (f x) = ∏ y, h y (f y) := by
    intro f
    simp only [hh, pF]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  simp only [e1]
  rw [← Fintype.prod_sum h]
  have e2 : ∀ y, ∑ b, h y b = if y = x then ∑ b, pA b * φ b else 1 := by
    intro y
    simp only [hh]
    split_ifs with hy
    · rfl
    · simp only [mul_one]; exact hpA.2
  simp only [e2]
  rw [Finset.prod_ite_eq']
  simp

end Aux_BoundedEntropyGames_ConvRate_eq_A_9

open BoundedEntropyGames.ConvRate Aux_BoundedEntropyGames_ConvRate_eq_A_9 in
theorem solution {𝒳 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒜] [DecidableEq 𝒜]
    (pA : 𝒜 → ℝ) (hpA : IsPMF pA) (g : 𝒳 → ℝ) (a : 𝒜) :
    ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)|
        ≤ 2 * pA a * (1 - pA a) * ∑ x, |g x| ∧
      ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)|
        ≤ 2 * pA a * ∑ x, |g x| := by
  set p := pA a with hp
  have hp0 : 0 ≤ p := hpA.1 a
  have hp1 : p ≤ 1 := by
    rw [hp, ← hpA.2]
    exact Finset.single_le_sum (f := pA) (fun b _ => hpA.1 b) (Finset.mem_univ a)
  have hpF : ∀ f : 𝒳 → 𝒜, 0 ≤ pF pA f := fun f => Finset.prod_nonneg fun y _ => hpA.1 _
  have habs : ∀ b : 𝒜, |(if b = a then (1 : ℝ) else 0) - p| = if b = a then 1 - p else p := by
    intro b
    split_ifs
    · exact abs_of_nonneg (by linarith)
    · rw [zero_sub, abs_neg, abs_of_nonneg hp0]
  have hmarg : ∀ x : 𝒳, ∑ f : 𝒳 → 𝒜, pF pA f * |(if f x = a then (1 : ℝ) else 0) - p| =
      2 * p * (1 - p) := by
    intro x
    rw [marginal pA hpA (fun b => |(if b = a then (1 : ℝ) else 0) - p|) x]
    simp only [habs]
    have : ∀ b, pA b * (if b = a then 1 - p else p) =
        pA b * p + (if b = a then pA b * (1 - 2 * p) else 0) := by
      intro b; split_ifs <;> ring
    simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul, hpA.2, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [← hp]
    ring
  have hmain : ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)|
      ≤ 2 * pA a * (1 - pA a) * ∑ x, |g x| := by
    calc ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)|
        ≤ ∑ f : 𝒳 → 𝒜, pF pA f * ∑ x, |g x| * |(if f x = a then (1 : ℝ) else 0) - p| := by
          refine Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left ?_ (hpF f)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [abs_mul]
      _ = ∑ x, |g x| * ∑ f : 𝒳 → 𝒜, pF pA f * |(if f x = a then (1 : ℝ) else 0) - p| := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun f _ => ?_
          ring
      _ = 2 * pA a * (1 - pA a) * ∑ x, |g x| := by
          simp only [hmarg]
          rw [← Finset.sum_mul, ← hp]
          ring
  refine ⟨hmain, hmain.trans ?_⟩
  have : 0 ≤ ∑ x, |g x| := Finset.sum_nonneg fun x _ => abs_nonneg _
  rw [← hp]
  nlinarith [mul_nonneg (mul_nonneg hp0 hp0) this]
