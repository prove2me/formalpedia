-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:10:20.518904+00:00
-- url     : https://prove2.me/submissions/5d3d5b9e-701f-4b59-87cb-5b0c6bacbf0b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (x η : ℝ) (hx : 0 < x) (hη : 0 < η) :
    ∃ (δ R : ℕ → ℝ),
      (∀ k, 0 < δ k ∧ δ k < x ∧ x < R k) ∧
      (∀ k, δ k ≤ η) ∧ Antitone δ ∧ Monotone R ∧
      Tendsto δ atTop (𝓝 0) ∧ Tendsto R atTop atTop := by 
  let a := min x η / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hax : a < x := by dsimp [a]; linarith [min_le_left x η]
  have haη : a ≤ η := by dsimp [a]; linarith [min_le_right x η]
  let δ : ℕ → ℝ := fun k => a / ((k : ℝ) + 1)
  let R : ℕ → ℝ := fun k => x + (k : ℝ) + 1
  have hδa (k : ℕ) : δ k ≤ a := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).2
    nlinarith [mul_nonneg ha.le (Nat.cast_nonneg (α := ℝ) k)]
  refine ⟨δ, R, ?_, fun k => (hδa k).trans haη, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨by dsimp [δ]; positivity, (hδa k).trans_lt hax, by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) k]⟩
  · intro i j hij
    dsimp [δ]
    exact div_le_div_of_nonneg_left ha.le (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
  · intro i j hij
    dsimp [R]
    have h : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  · have h := (tendsto_const_div_atTop_nhds_zero_nat a).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  · exact tendsto_atTop_atTop_of_monotone
      (fun i j hij => by dsimp [R]; gcongr) (fun b => by
        obtain ⟨n, hn⟩ := exists_nat_gt (b - x)
        exact ⟨n, by dsimp [R]; linarith⟩)
