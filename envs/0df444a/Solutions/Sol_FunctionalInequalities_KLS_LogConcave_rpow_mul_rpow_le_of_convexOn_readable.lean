-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.rpow_mul_rpow_le_of_convexOn_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:26:57.468536+00:00
-- url     : https://prove2.me/submissions/2deda083-175c-4e79-8cd9-616cff5fd778

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted

noncomputable section
open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- For convex `W` and `Z > 0`, the normalized weight `e^{-W} / Z` is log-concave:
`ρ(x)^t ρ(y)^{1-t} ≤ ρ(t x + (1 - t) y)` for `0 < t < 1`. -/
theorem solution {W : V → ℝ} (hconv : ConvexOn ℝ Set.univ W) {Z : ℝ}
    (hZ : 0 < Z) (x y : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (Real.exp (-W x) / Z) ^ t * (Real.exp (-W y) / Z) ^ (1 - t) ≤
      Real.exp (-W (t • x + (1 - t) • y)) / Z := by
  have hAx : 0 < Real.exp (-W x) / Z :=
    div_pos (Real.exp_pos _) hZ
  have hAy : 0 < Real.exp (-W y) / Z :=
    div_pos (Real.exp_pos _) hZ
  have hlogx :
      Real.log (Real.exp (-W x) / Z) = -W x - Real.log Z := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ), Real.log_exp]
  have hlogy :
      Real.log (Real.exp (-W y) / Z) = -W y - Real.log Z := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ), Real.log_exp]
  have hleft :
      (Real.exp (-W x) / Z) ^ t * (Real.exp (-W y) / Z) ^ (1 - t) =
        Real.exp ((-W x - Real.log Z) * t +
          (-W y - Real.log Z) * (1 - t)) := by
    rw [Real.rpow_def_of_pos hAx, Real.rpow_def_of_pos hAy, hlogx, hlogy,
      ← Real.exp_add]
  have hright :
      Real.exp (-W (t • x + (1 - t) • y)) / Z =
        Real.exp (-W (t • x + (1 - t) • y) - Real.log Z) := by
    calc
      Real.exp (-W (t • x + (1 - t) • y)) / Z =
          Real.exp (-W (t • x + (1 - t) • y)) / Real.exp (Real.log Z) := by
            rw [Real.exp_log hZ]
      _ = Real.exp (-W (t • x + (1 - t) • y) - Real.log Z) := by
        rw [Real.exp_sub]
  rw [hleft, hright]
  apply Real.exp_le_exp.mpr
  have hW0 :=
    hconv.2 (Set.mem_univ x) (Set.mem_univ y) ht0.le
      (by linarith : 0 ≤ 1 - t) (by ring : t + (1 - t) = 1)
  have hW :
      W (t • x + (1 - t) • y) ≤ t * W x + (1 - t) * W y := by
    simpa [smul_eq_mul] using hW0
  calc
    (-W x - Real.log Z) * t + (-W y - Real.log Z) * (1 - t) =
        -(t * W x + (1 - t) * W y) - Real.log Z := by ring
    _ ≤ -W (t • x + (1 - t) • y) - Real.log Z := by linarith
