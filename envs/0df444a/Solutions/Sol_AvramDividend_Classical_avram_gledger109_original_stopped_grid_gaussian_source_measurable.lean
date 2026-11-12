-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger109_original_stopped_grid_gaussian_source_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:37:11.556415+00:00
-- url     : https://prove2.me/submissions/6e978948-9438-4a6d-bfdd-d014d7b04d6f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger75_original_stopped_levy_and_rightDividend_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped physical Gaussian source is measurable at every finite grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (r : ℕ) :
    Measurable (fun ω : Ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((r : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      Finset.sum (Finset.range (r + 1)) (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))))) := by
  have hDstrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hwM : Measurable w :=
    avram_wave6_04b_cap_extension_measurable_of_zero_negative
      w w (⊤ : ℝ≥0∞) hw_cont hw_neg
      (by intro _ _; rfl) (by intro h; exact False.elim (h rfl))
  have hρNN : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((r : ℝ≥0) + 1)
  let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
  let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
  let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (v i ω) ω - rightLimit D (v i ω) ω
  let Z : ℕ → Ω → ℝ := fun i ω => x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
  have hObs := avram_gledger75_original_stopped_levy_and_rightDividend_joint_measurable
    X hX D hDstrat ρ hρstop Δ
  have hv (i : ℕ) : Measurable (v i) := by
    dsimp [v]
    exact measurable_const.min hρNN
  have hE (i : ℕ) : Measurable (E i) := by
    dsimp [E]
    exact Real.continuous_exp.measurable.comp
      ((measurable_const.mul (hv i).coe_nnreal_real).neg)
  have hY (i : ℕ) : Measurable (Y i) := by
    dsimp [Y]
    exact (measurable_const.add (hObs i).1).sub (hObs i).2
  have hZ (i : ℕ) : Measurable (Z i) := by
    dsimp [Z]
    exact (measurable_const.add (hObs (i + 1)).1).sub (hObs i).2
  have hSum : Measurable (fun ω =>
      Finset.sum (Finset.range (r + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
          E (i + 1) ω * (w (Z i ω) - w (Y i ω)))) := by
    apply Finset.measurable_sum
    intro i hi
    exact ((hE (i + 1)).sub (hE i)).mul (hwM.comp (hY i)) |>.add
      ((hE (i + 1)).mul ((hwM.comp (hZ i)).sub (hwM.comp (hY i))))
  simpa only [Δ, v, E, Y, Z] using hSum
