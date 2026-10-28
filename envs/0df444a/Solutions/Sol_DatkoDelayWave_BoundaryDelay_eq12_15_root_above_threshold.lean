-- Prove2me | solution 1 for DatkoDelayWave.BoundaryDelay.eq12_15_root_above_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:23:59.588081+00:00
-- url     : https://prove2.me/submissions/50dc87be-dba0-474c-a0dc-645cb71987fb

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

-- carved verbatim out of submission 9e78ff97-3a87-4a96-9f66-6a86542faea0, lines 709-770

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
open Complex
open DatkoDelayWave
open DatkoDelayWave.BoundaryDelay
open Set Filter Metric
open scoped Topology

theorem K_pos (a : ℝ) : 0 < K a := Real.exp_pos _

theorem exp_odd_pi (j : ℕ) :
    Complex.exp (-((2 * (j : ℂ) + 1) * (Real.pi : ℂ) * Complex.I)) = -1 := by
  have h : -((2 * (j : ℂ) + 1) * (Real.pi : ℂ) * Complex.I)
      = ((-(j : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + -((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem solution (a k : ℝ) (ha : 0 ≤ a)
    (hkK : (1 - K a) / (1 + K a) < k) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ ω₁ : ℝ, 0 < ω₁ ∧
      f a k (2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1))
        ((ω₁ : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2) = 0 := by
  set ε : ℝ := 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) with hε
  have hK0 := K_pos a
  have hk0 : (1 - K a) < k * (1 + K a) := (div_lt_iff₀ (by positivity : 0 < 1 + K a)).mp hkK
  set g : ℝ → ℝ := fun x => (1 - K a * Real.exp (-2 * x))
    - k * Real.exp (-ε * x) * (1 + K a * Real.exp (-2 * x)) with hg
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hg0 : g 0 < 0 := by simp only [hg]; simp; linarith
  have e1 : Filter.Tendsto (fun x : ℝ => Real.exp (-2 * x)) Filter.atTop (nhds 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa [Function.comp_def, neg_mul] using this
  have hεpos : 0 < ε := by rw [hε]; positivity
  have e2 : Filter.Tendsto (fun x : ℝ => Real.exp (-ε * x)) Filter.atTop (nhds 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop hεpos)
    simpa [Function.comp_def, neg_mul] using this
  have hlim : Filter.Tendsto g Filter.atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub ((tendsto_const_nhds (x := K a)).mul e1) |>.sub
      (((tendsto_const_nhds (x := k)).mul e2).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_nhds (x := K a)).mul e1)))
    have h1 : (1 - K a * 0 - k * 0 * (1 + K a * 0)) = 1 := by ring
    rw [h1] at this
    exact this
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp (hlim.eventually (lt_mem_nhds (zero_lt_one' ℝ)))
  have hX' := hX (max X 1) (le_max_left _ _)
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc (le_trans zero_le_one (le_max_right X 1))
    hgc.continuousOn ⟨hg0.le, hX'.le⟩
  have hxpos : 0 < x := by
    rcases hx.1.eq_or_lt with h0 | h0
    · rw [← h0] at hgx; linarith
    · exact h0
  refine ⟨x, hxpos, ?_⟩
  have c1 : Complex.exp (-2 * ((x : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2))
      = -((Real.exp (-2 * x) : ℝ) : ℂ) := by
    have : -2 * ((x : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2)
        = ((-2 * x : ℝ) : ℂ) + (-((2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I)) := by
      push_cast; ring
    rw [this, Complex.exp_add, exp_odd_pi n, ← Complex.ofReal_exp]; ring
  have c2 : Complex.exp (-(ε : ℂ) * ((x : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2))
      = -((Real.exp (-ε * x) : ℝ) : ℂ) := by
    have hn0 : (2 * (n : ℂ) + 1) ≠ 0 := by
      have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      exact_mod_cast this
    have : -(ε : ℂ) * ((x : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2)
        = ((-ε * x : ℝ) : ℂ) + (-((2 * (m : ℂ) + 1) * (Real.pi : ℂ) * Complex.I)) := by
      rw [hε]; push_cast; field_simp; ring
    rw [this, Complex.exp_add, exp_odd_pi m, ← Complex.ofReal_exp]; ring
  have hf : f a k ε ((x : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2)
      = ((g x : ℝ) : ℂ) := by
    unfold f
    rw [c1, c2]
    simp only [hg]
    push_cast
    ring
  rw [hf, hgx]; simp

end
