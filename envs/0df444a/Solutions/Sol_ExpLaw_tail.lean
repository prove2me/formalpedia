-- Prove2me | solution 1 for ExpLaw.tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:42.338468+00:00
-- url     : https://prove2.me/submissions/d514940e-4a08-4203-bf30-3f43f4ee1d4d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real

open MeasureTheory ProbabilityTheory

namespace CohenPriceFairness.LocalWelfare.Sol_exp_demand

instance ec_noAtoms (l : ℝ) : NullSingletonClass (expMeasure l) :=
  ⟨fun x => withDensity_absolutelyContinuous _ _ (measure_singleton x)⟩

end CohenPriceFairness.LocalWelfare.Sol_exp_demand

open CohenPriceFairness.LocalWelfare
open CohenPriceFairness.LocalWelfare.Sol_exp_demand

/-- The tail `μ[p, ∞)` equals `μ(p, ∞)` (no atoms), which is the strict upper-tail survival law
`AvramDividend.Classical.avram_ws01e_b_expMeasure_strict_survival_real`. -/
theorem solution {l p : ℝ} (hl : 0 < l) (hp : 0 ≤ p) :
    ((expMeasure l) (Set.Ici p)).toReal = Real.exp (-(l * p)) := by
  have h1 : (expMeasure l) (Set.Ici p) = (expMeasure l) (Set.Ioi p) :=
    (measure_congr Ioi_ae_eq_Ici).symm
  rw [h1, AvramDividend.Classical.avram_ws01e_b_expMeasure_strict_survival_real l p hl hp,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

