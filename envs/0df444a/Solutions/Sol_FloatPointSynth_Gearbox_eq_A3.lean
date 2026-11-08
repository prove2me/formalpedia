-- Prove2me | solution 1 for FloatPointSynth.Gearbox.eq_A3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:37:27.672707+00:00
-- url     : https://prove2.me/submissions/bdb088e1-e14e-4d37-9cd3-cc577103857a

import Mathlib
import Definitions.Def_FloatPointSynth_Gearbox_Cost

open scoped ENNReal

namespace Aux_FPSA3

open FloatPointSynth.Gearbox

theorem mean_pure (c : ℕ) : pmfMean (PMF.pure c) = c := by
  unfold pmfMean
  rw [tsum_eq_single c]
  · simp
  · intro n hn; simp [PMF.pure_apply, hn]

theorem mean_bind (μ : PMF ℕ) (f : ℕ → PMF ℕ) :
    pmfMean (μ.bind f) = ∑' a, μ a * pmfMean (f a) := by
  unfold pmfMean
  simp only [PMF.bind_apply]
  have h : ∀ n : ℕ, (∑' a, μ a * f a n) * (n : ℝ≥0∞) = ∑' a, μ a * (f a n * n) := by
    intro n
    rw [← ENNReal.tsum_mul_right]
    congr 1; funext a; ring
  simp only [h]
  rw [ENNReal.tsum_comm]
  congr 1; funext a
  rw [ENNReal.tsum_mul_left]

theorem mean_map_add (a : ℕ) (ν : PMF ℕ) : pmfMean (ν.map (a + ·)) = a + pmfMean ν := by
  rw [← PMF.bind_pure_comp, mean_bind]
  simp only [Function.comp, mean_pure]
  push_cast
  simp only [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rfl

theorem mean_iid (μ : PMF ℕ) (k : ℕ) : pmfMean (iidSum μ k) = k * pmfMean μ := by
  induction k with
  | zero => simp [iidSum, mean_pure]
  | succ k ih =>
    simp only [iidSum]
    rw [mean_bind]
    simp only [mean_map_add, ih]
    simp only [mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    unfold pmfMean
    push_cast
    ring

end Aux_FPSA3

open FloatPointSynth.Gearbox Aux_FPSA3 in
theorem solution (U : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (hq : 2 ≤ q) :
    pmfMean (xLaw U q) =
      2 * pmfMean (geomPos (levelProb U q)) * pmfMean (xLaw U (q - 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  rw [show r + 2 - 1 = r + 1 by omega]
  simp only [xLaw]
  rw [mean_bind]
  simp only [mean_iid]
  push_cast
  have : ∀ N : ℕ, (geomPos (levelProb U (r + 2))) N * (2 * (N : ℝ≥0∞) * pmfMean (xLaw U (r + 1))) =
      (geomPos (levelProb U (r + 2))) N * (N : ℝ≥0∞) * (2 * pmfMean (xLaw U (r + 1))) := by
    intro N; ring
  simp only [this]
  rw [ENNReal.tsum_mul_right]
  unfold pmfMean
  ring
