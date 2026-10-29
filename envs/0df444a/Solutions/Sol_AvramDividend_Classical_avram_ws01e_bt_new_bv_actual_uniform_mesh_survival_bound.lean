-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_bv_actual_uniform_mesh_survival_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:35:54.492059+00:00
-- url     : https://prove2.me/submissions/3ab19ac5-d2e4-4829-a145-984ebc29a87c

import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_bv_mesh_grid_calibration
import Theorems.Thm_AvramDividend_Classical_bv_survival_mesh_bound_normalized_exponent
import Theorems.Thm_AvramDividend_Classical_bv_actual_grid_exponential_integrability
import Theorems.Thm_AvramDividend_Classical_bv_actual_survival_deficit_integrable
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Probability.Process.Adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators

/-- The actual BV Lévy grid has all mesh, measurability, and integrability
premises required for the accepted normalised survival bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : 0 < T)
    (N : ℕ) (hN : 0 < N)
    (hLarge : 2 * X.drift * (T : ℝ) ≤ (N : ℝ)) :
    (let δ : ℝ≥0 := T / (N : ℝ≥0)
     let a : ℝ := X.drift * (δ : ℝ)
     let θ : ℝ := 1 / (2 * a)
     (∫ ω, {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
       (fun ω => (T : ℝ) * X.drift - X.X T ω) ω ∂P) ≤
       (4 * X.drift * (T : ℝ)) *
         (1 - Real.exp (-((δ : ℝ) * (X.drift * θ - X.ψ θ))))) := by
  let δ : ℝ≥0 := T / (N : ℝ≥0)
  let ts : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * δ
  let a : ℝ := X.drift * (δ : ℝ)
  change (∫ ω, {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
      (fun ω => (T : ℝ) * X.drift - X.X T ω) ω ∂P) ≤
    (4 * X.drift * (T : ℝ)) *
      (1 - Real.exp (-((δ : ℝ) *
        (X.drift * (1 / (2 * a)) - X.ψ (1 / (2 * a))))))
  have hd : 0 < X.drift := (bv_standing_drift_pos X hStanding hBV).1
  have hgeom := avram_ws01e_bt_new_bv_mesh_grid_calibration
    X.drift hd T hT N hN hLarge
  change 0 < a ∧ ts N = T ∧
    (∀ k : ℕ, k < N → ts (k + 1) - ts k = δ) ∧
    (∀ k : ℕ, k < N → ts (k + 1) ≤ T) ∧
    1 ≤ 1 / (2 * a) ∧
    (δ : ℝ) * (1 / (2 * a)) = 1 / (2 * X.drift) ∧
    4 * a * (N : ℝ) = 4 * X.drift * (T : ℝ) at hgeom
  rcases hgeom with ⟨ha, htsN, hStep, hWithin, hRate, _, hPref⟩
  have htsStep (k : ℕ) : ts (k + 1) = ts k + δ := by
    dsimp [ts]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hOrder (k : ℕ) (_ : k < N) : ts k ≤ ts (k + 1) := by
    rw [htsStep]
    exact le_add_of_nonneg_right bot_le
  have hStepReal (k : ℕ) (_ : k < N) :
      (ts (k + 1) : ℝ) - (ts k : ℝ) = (δ : ℝ) := by
    rw [htsStep]
    push_cast <;> ring
  let D : ℕ → Ω → ℝ := fun k ω =>
    X.drift * (ts k : ℝ) - X.X (ts k) ω
  have hD (k : ℕ) (ω : Ω) :
      D k ω = X.drift * (ts k : ℝ) - X.X (ts k) ω := rfl
  have hts0 : ts 0 = 0 := by simp [ts]
  have hEnd (ω : Ω) :
      D N ω - D 0 ω = (T : ℝ) * X.drift - X.X T ω := by
    dsimp [D]
    rw [htsN, hts0]
    simp [X.X_zero] <;> ring
  have hDMeas (k : ℕ) : Measurable (D k) := by
    change Measurable (fun ω =>
      X.drift * (ts k : ℝ) - X.X (ts k) ω)
    exact measurable_const.sub ((X.adapted (ts k)).mono (𝓕.le (ts k)) le_rfl)
  have hCellMeas (k : ℕ) (_ : k < N) :
      AEStronglyMeasurable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P := by
    have hGap : Measurable (fun ω =>
        D (k + 1) ω - D k ω) :=
      (hDMeas (k + 1)).sub (hDMeas k)
    exact (measurable_const.sub
      (Real.measurable_exp.comp (measurable_const.mul hGap))).aestronglyMeasurable
  have hInt := bv_actual_grid_exponential_integrability
    X hBV N ts D hD hOrder a ha hCellMeas
  have hLeft : Integrable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => D N ω - D 0 ω)) P := by
    simpa only [hEnd] using
      (bv_actual_survival_deficit_integrable X hStanding hBV T)
  exact bv_survival_mesh_bound_normalized_exponent
    X hBV T N ts δ D hD hEnd hOrder hWithin hStep hStepReal
    a (4 * X.drift * (T : ℝ)) ha rfl hPref hRate
    hLeft hInt.2 hInt.1
