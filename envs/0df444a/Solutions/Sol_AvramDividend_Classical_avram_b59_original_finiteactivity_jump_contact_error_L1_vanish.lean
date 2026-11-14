-- Prove2me | solution 1 for AvramDividend.Classical.avram_b59_original_finiteactivity_jump_contact_error_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:40:31.575019+00:00
-- url     : https://prove2.me/submissions/0f4c8baa-06d7-4b3d-bf18-6d150aaf9b44

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b58_original_selected_negative_jump_cells_uniform_count_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-exact finite-activity jump-contact errors vanish on any event under a vanishing mesh factor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (A : Set Ω)
    (J : ℕ → Ω → Finset ℕ)
    (hJmeas : ∀ m, Measurable (fun ω : Ω => ((J m ω).card : ℝ)))
    (hJdom : ∀ m ω, ((J m ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal)
    (E : ℕ → Ω → ℝ) (hEmeas : ∀ m, Measurable (E m))
    (η : ℕ → ℝ) (hη : ∀ m, 0 ≤ η m)
    (hηlim : Tendsto η atTop (𝓝 0))
    (hEbound : ∀ m ω, |E m ω| ≤ η m * ((J m ω).card : ℝ)) :
    Tendsto (fun m => ∫ ω in A, |E m ω| ∂P) atTop (𝓝 0) := by 
  classical
  let K : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
  have hJump (m : ℕ) :
      Integrable (fun ω => ((J m ω).card : ℝ)) P ∧
      (∫ ω in A, ((J m ω).card : ℝ) ∂P) ≤ K :=
    avram_b58_original_selected_negative_jump_cells_uniform_count_L1
      X hFinite T A (J m) (hJmeas m) (hJdom m)
  have hEI (m : ℕ) : Integrable (fun ω => |E m ω|) P := by
    have hDom : Integrable (fun ω => η m * ((J m ω).card : ℝ)) P :=
      (hJump m).1.const_mul (η m)
    exact hDom.mono_nonneg (hEmeas m).abs.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => abs_nonneg _))
      (Filter.Eventually.of_forall (hEbound m))
  have hBound (m : ℕ) :
      (∫ ω in A, |E m ω| ∂P) ≤ η m * K := by
    calc
      (∫ ω in A, |E m ω| ∂P) ≤
          ∫ ω in A, η m * ((J m ω).card : ℝ) ∂P :=
        integral_mono (hEI m).integrableOn
          ((hJump m).1.const_mul (η m)).integrableOn
          (hEbound m)
      _ = η m * (∫ ω in A, ((J m ω).card : ℝ) ∂P) := by
        rw [integral_const_mul]
      _ ≤ η m * K :=
        mul_le_mul_of_nonneg_left (hJump m).2 (hη m)
  have hLim : Tendsto (fun m => η m * K) atTop (𝓝 0) := by
    simpa using hηlim.mul_const K
  apply Filter.Tendsto.squeeze
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    hLim
  · intro m
    exact integral_nonneg (fun ω => abs_nonneg _)
  · intro m
    exact hBound m
