-- Prove2me | solution 1 for BirkhoffGlobalSection.winding_arithmetic_bundle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T12:49:01.718809+00:00
-- url     : https://prove2.me/submissions/500a7c68-4d30-4083-906f-d086f9b08a03

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false



private theorem lower_winding_interval_threshold_iff (a b : ℝ) (k : ℤ)
    (hab : a ≤ b) (hwidth : b - a < 1) :
    2 * k + 1 ≤ Int.ceil a + Int.ceil b - 1 ↔ (k : ℝ) < a := by
  constructor
  · intro h
    by_contra! ha
    have hca : Int.ceil a ≤ k := Int.ceil_le.mpr ha
    have hcb : Int.ceil b ≤ k + 1 := by
      apply Int.ceil_le.mpr
      push_cast
      linarith
    omega
  · intro ha
    have hca : k < Int.ceil a := Int.lt_ceil.mpr ha
    have hcb : k < Int.ceil b := Int.lt_ceil.mpr (lt_of_lt_of_le ha hab)
    omega

private theorem lower_winding_interval_ge_three_iff (a b : ℝ)
    (hab : a ≤ b) (hwidth : b - a < 1) :
    (3 : ℤ) ≤ Int.ceil a + Int.ceil b - 1 ↔ 1 < a := by
  simpa using lower_winding_interval_threshold_iff a b 1 hab hwidth

private theorem lower_winding_interval_noninteger (a b : ℝ) (k : ℤ)
    (ha : (k : ℝ) < a) (hab : a ≤ b) (hb : b < (k : ℝ) + 1) :
    Int.ceil a + Int.ceil b - 1 = 2 * k + 1 := by
  have hca : Int.ceil a = k + 1 := by
    apply le_antisymm
    · apply Int.ceil_le.mpr
      push_cast
      linarith
    · have h := Int.lt_ceil.mpr ha
      omega
  have hcb : Int.ceil b = k + 1 := by
    apply le_antisymm
    · apply Int.ceil_le.mpr
      push_cast
      linarith
    · have h := Int.lt_ceil.mpr (lt_of_lt_of_le ha hab)
      omega
  rw [hca, hcb]
  ring

private theorem lower_winding_interval_integer_crossing (a b : ℝ) (k : ℤ)
    (ha : a < (k : ℝ)) (hb : (k : ℝ) < b) (hwidth : b - a < 1) :
    Int.ceil a + Int.ceil b - 1 = 2 * k := by
  have hca : Int.ceil a = k := by
    apply le_antisymm (Int.ceil_le.mpr ha.le)
    apply Int.le_ceil_iff.mpr
    linarith
  have hcb : Int.ceil b = k + 1 := by
    apply le_antisymm
    · apply Int.ceil_le.mpr
      push_cast
      linarith
    · have h := Int.lt_ceil.mpr hb
      omega
  rw [hca, hcb]
  ring

private theorem lower_winding_interval_integer_upper (a : ℝ) (k : ℤ)
    (ha : a ≤ (k : ℝ)) (hwidth : (k : ℝ) - a < 1) :
    Int.ceil a + Int.ceil (k : ℝ) - 1 = 2 * k - 1 := by
  have hca : Int.ceil a = k := by
    apply le_antisymm (Int.ceil_le.mpr ha)
    apply Int.le_ceil_iff.mpr
    linarith
  rw [hca, Int.ceil_intCast]
  ring

private theorem lower_winding_interval_integer_lower (b : ℝ) (k : ℤ)
    (hb : (k : ℝ) < b) (hwidth : b - (k : ℝ) < 1) :
    Int.ceil (k : ℝ) + Int.ceil b - 1 = 2 * k := by
  have hcb : Int.ceil b = k + 1 := by
    apply le_antisymm
    · apply Int.ceil_le.mpr
      push_cast
      linarith
    · have h := Int.lt_ceil.mpr hb
      omega
  rw [Int.ceil_intCast, hcb]
  ring

private theorem lower_winding_interval_left_stable (a b : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      Int.ceil (a - ε) + Int.ceil (b - ε) - 1 = Int.ceil a + Int.ceil b - 1 := by
  have ha : (Int.ceil a : ℝ) - 1 < a := (Int.ceil_eq_iff.mp rfl).1
  have hb : (Int.ceil b : ℝ) - 1 < b := (Int.ceil_eq_iff.mp rfl).1
  refine ⟨min (a - ((Int.ceil a : ℝ) - 1)) (b - ((Int.ceil b : ℝ) - 1)),
    lt_min (by linarith) (by linarith), ?_⟩
  intro ε hε hδ
  have hεa := lt_of_lt_of_le hδ (min_le_left _ _)
  have hεb := lt_of_lt_of_le hδ (min_le_right _ _)
  have hca : Int.ceil (a - ε) = Int.ceil a := Int.ceil_eq_iff.mpr
    ⟨by linarith, by linarith [Int.le_ceil a]⟩
  have hcb : Int.ceil (b - ε) = Int.ceil b := Int.ceil_eq_iff.mpr
    ⟨by linarith, by linarith [Int.le_ceil b]⟩
  rw [hca, hcb]

theorem solution :
(∀ (a b : ℝ) (k : ℤ)
    (hab : a ≤ b) (hwidth : b - a < 1),
    2 * k + 1 ≤ Int.ceil a + Int.ceil b - 1 ↔ (k : ℝ) < a) ∧
(∀ (a b : ℝ)
    (hab : a ≤ b) (hwidth : b - a < 1),
    (3 : ℤ) ≤ Int.ceil a + Int.ceil b - 1 ↔ 1 < a) ∧
(∀ (a b : ℝ) (k : ℤ)
    (ha : (k : ℝ) < a) (hab : a ≤ b) (hb : b < (k : ℝ) + 1),
    Int.ceil a + Int.ceil b - 1 = 2 * k + 1) ∧
(∀ (a b : ℝ) (k : ℤ)
    (ha : a < (k : ℝ)) (hb : (k : ℝ) < b) (hwidth : b - a < 1),
    Int.ceil a + Int.ceil b - 1 = 2 * k) ∧
(∀ (a : ℝ) (k : ℤ)
    (ha : a ≤ (k : ℝ)) (hwidth : (k : ℝ) - a < 1),
    Int.ceil a + Int.ceil (k : ℝ) - 1 = 2 * k - 1) ∧
(∀ (b : ℝ) (k : ℤ)
    (hb : (k : ℝ) < b) (hwidth : b - (k : ℝ) < 1),
    Int.ceil (k : ℝ) + Int.ceil b - 1 = 2 * k) ∧
(∀ (a b : ℝ),
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      Int.ceil (a - ε) + Int.ceil (b - ε) - 1 = Int.ceil a + Int.ceil b - 1) := by
  exact ⟨@lower_winding_interval_threshold_iff, ⟨@lower_winding_interval_ge_three_iff, ⟨@lower_winding_interval_noninteger, ⟨@lower_winding_interval_integer_crossing, ⟨@lower_winding_interval_integer_upper, ⟨@lower_winding_interval_integer_lower, @lower_winding_interval_left_stable⟩⟩⟩⟩⟩⟩
