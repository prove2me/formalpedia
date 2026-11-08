-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord9_original_zero_uniform_cell_nonintegrable_of_profile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:48:39.968277+00:00
-- url     : https://prove2.me/submissions/e248497c-78ee-4965-ac12-912f752f4471

import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T x : ℝ) (hT : 0 < T)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hruin : ∀ ω, (0 : ℝ≥0∞) < ruinTime X x D ω)
    (hpositive : ∀ ω, 0 < x - rightLimit D 0 ω)
    (hcap : ∀ ω, ENNReal.ofReal (x - rightLimit D 0 ω) < C)
    (hmeas : AEStronglyMeasurable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (hnonint : ¬ Integrable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P) :
    ¬ HasFiniteIntegral (fun ω =>
      let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0
      if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ ENNReal.ofReal Z < C then
        Real.exp (-(q * (0 : ℝ))) *
          (X.generator w Z - q * w Z) * (T / 2)
      else 0) P := by
  intro hfin
  let g : Ω → ℝ := fun ω =>
    X.generator w (x - rightLimit D 0 ω) -
      q * w (x - rightLimit D 0 ω)
  have hleft (ω : Ω) :
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0 =
        x - rightLimit D 0 ω := by
    have hmin : IsBot (0 : ℝ≥0) := by
      change IsBot (⊥ : ℝ≥0)
      exact isBot_bot
    simpa [X.X_zero] using
      (leftLim_eq_of_isBot
        (f := fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (ha := hmin))
  have hcell (ω : Ω) :
      (let Z := Function.leftLim
         (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0
       if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
           0 < Z ∧ ENNReal.ofReal Z < C then
         Real.exp (-(q * (0 : ℝ))) *
           (X.generator w Z - q * w Z) * (T / 2)
       else 0) = g ω * (T / 2) := by
    simp [hleft ω, hruin ω, hpositive ω, hcap ω, g]
  have heq :
      (fun ω : Ω =>
        let Z := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0
        if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z ∧ ENNReal.ofReal Z < C then
          Real.exp (-(q * (0 : ℝ))) *
            (X.generator w Z - q * w Z) * (T / 2)
        else 0) = (fun ω => g ω * (T / 2)) := by
    funext ω
    exact hcell ω
  rw [heq] at hfin
  have hmeas_g : AEStronglyMeasurable g P := hmeas
  have hscaled : Integrable (fun ω => g ω * (T / 2)) P :=
    ⟨hmeas_g.mul_const _, hfin⟩
  have hunit : IsUnit (T / 2 : ℝ) :=
    isUnit_iff_ne_zero.mpr (by positivity)
  exact hnonint ((integrable_mul_const_iff hunit g).mp hscaled)
