-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_admissible_source_jump_every_prefix_without_hjump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:26:11.324777+00:00
-- url     : https://prove2.me/submissions/859052fa-3560-408d-b4fd-a3293645f4d4

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_arbitrary_source_jump_sequence_every_finite_prefix_full_initial_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- Every finite original source-before-payment jump prefix obeys the full initial atom HJB bound with hjump derived from admissibility. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v < 0, w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (x q : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℕ → ℝ≥0)
    (hTimes : ∀ n, 0 < t n ∧ (t n : ℝ≥0∞) < ruinTime X x D ω)
    (hValid : ∀ n,
      X.X (t n) ω ≤ Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) ∧
      0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) - D (t n) ω ∧
      ENNReal.ofReal
        (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) - D (t n) ω) ≤ C) :
    let J : ℕ → ℝ := fun i =>
      Real.exp (-(q * (t i : ℝ))) *
        ((w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t i) -
              D (t i) ω)) +
          (rightLimit D (t i) ω - D (t i) ω))
    ∀ n : ℕ, (w (x - rightLimit D 0 ω) + rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n, J i) ≤ w x := by
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hJump :=
    avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
      X hX hBV C hC w hw_cont hw_smooth hw_grad
      x hx hxc D hD
  exact
    avram_wave7_02_original_arbitrary_source_jump_sequence_every_finite_prefix_full_initial_budget
      X C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
      x q D hStrat hJump ω t hTimes hValid
