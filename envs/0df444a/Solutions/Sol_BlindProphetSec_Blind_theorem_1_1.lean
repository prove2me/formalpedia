-- Prove2me | solution 1 for BlindProphetSec.Blind.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:13:38.316258+00:00
-- url     : https://prove2.me/submissions/822a352e-7831-4540-b45f-3bc55db7b67c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting
import Theorems.Thm_BlindProphetSec_Blind_corollary_4_4

open MeasureTheory

namespace BPSThm11

open BlindProphetSec.Blind

/-- On `[0, 1)`, `α_{α₁,…,α_m}(x) = α_{⌊x m⌋ + 1}`. -/
lemma pieceAlpha_eq (m : ℕ) (hm : 1 ≤ m) (a : ℕ → ℝ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    pieceAlpha m a x = a (⌊x * m⌋₊ + 1) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hxm : 0 ≤ x * m := mul_nonneg hx0 hmpos.le
  have hfl : ⌊x * m⌋₊ < m := by
    rw [Nat.floor_lt hxm]; nlinarith
  unfold pieceAlpha
  rw [Finset.sum_eq_single (⌊x * m⌋₊ + 1)]
  · rw [if_pos]
    push_cast
    constructor
    · rw [div_le_iff₀ hmpos]
      have := Nat.floor_le hxm
      linarith
    · rw [lt_div_iff₀ hmpos]
      exact Nat.lt_floor_add_one _
  · intro j hj hne
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hne
    have hj' := Finset.mem_Icc.mp hj
    rw [div_le_iff₀ hmpos] at h1
    rw [lt_div_iff₀ hmpos] at h2
    have : ⌊x * m⌋₊ = j - 1 := by
      rw [Nat.floor_eq_iff hxm]
      push_cast [Nat.cast_sub hj'.1]
      constructor <;> linarith
    omega
  · intro h
    exfalso; apply h
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- For `x ≥ 1`, `α_{α₁,…,α_m}(x) = 0`. -/
lemma pieceAlpha_ge_one (m : ℕ) (a : ℕ → ℝ) (x : ℝ) (hx : 1 ≤ x) : pieceAlpha m a x = 0 := by
  unfold pieceAlpha
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  rw [if_neg]
  rintro ⟨_, h2⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [lt_div_iff₀ hmpos] at h2
  have : (j : ℝ) ≤ m := by exact_mod_cast hj'.2
  nlinarith

lemma idx_mem (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ⌊x * m⌋₊ + 1 ∈ Set.Icc 1 m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hxm : 0 ≤ x * m := mul_nonneg hx0 hmpos.le
  have hfl : ⌊x * m⌋₊ < m := by
    rw [Nat.floor_lt hxm]; nlinarith
  exact ⟨by omega, by omega⟩

end BPSThm11

open BlindProphetSec.Blind BPSThm11 in
theorem solution :
    ∃ α : ℝ → ℝ, AntitoneOn α (Set.Icc 0 1) ∧ Set.MapsTo α (Set.Icc 0 1) (Set.Icc 0 1) ∧
      ∀ (n : ℕ) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)],
        (∀ i, μ i (Set.Iio 0) = 0) →
        ENNReal.ofReal (669 / 1000) * Emax μ ≤ blindValue α μ := by
  obtain ⟨m, hm, a, ha1, hanti, ham, H⟩ := corollary_4_4
  have hmm : m ∈ Set.Icc 1 m := ⟨hm, le_rfl⟩
  have h1m : 1 ∈ Set.Icc 1 m := ⟨le_rfl, hm⟩
  -- values of `a` on `[1, m]` lie in `[0, 1]`
  have hval : ∀ j ∈ Set.Icc 1 m, 0 ≤ a j ∧ a j ≤ 1 := by
    intro j hj
    exact ⟨le_trans ham (hanti hj hmm hj.2), le_trans (hanti h1m hj hj.1) ha1⟩
  refine ⟨pieceAlpha m a, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hy1 : y < 1
    · have hx1 : x < 1 := lt_of_le_of_lt hxy hy1
      rw [pieceAlpha_eq m hm a x hx.1 hx1, pieceAlpha_eq m hm a y hy.1 hy1]
      apply hanti (idx_mem m hm x hx.1 hx1) (idx_mem m hm y hy.1 hy1)
      have hmpos : (0 : ℝ) ≤ m := by positivity
      have := Nat.floor_le_floor (mul_le_mul_of_nonneg_right hxy hmpos)
      omega
    · rw [pieceAlpha_ge_one m a y (not_lt.mp hy1)]
      by_cases hx1 : x < 1
      · rw [pieceAlpha_eq m hm a x hx.1 hx1]
        exact (hval _ (idx_mem m hm x hx.1 hx1)).1
      · rw [pieceAlpha_ge_one m a x (not_lt.mp hx1)]
  · intro x hx
    by_cases hx1 : x < 1
    · rw [pieceAlpha_eq m hm a x hx.1 hx1]
      exact hval _ (idx_mem m hm x hx.1 hx1)
    · rw [pieceAlpha_ge_one m a x (not_lt.mp hx1)]
      exact ⟨le_rfl, zero_le_one⟩
  · intro n μ _ _ hnn
    exact le_trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by norm_num)) _) (H n μ hnn)
