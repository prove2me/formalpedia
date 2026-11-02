-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02a_original_jump_kernel_of_measurable_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:35:38.80528+00:00
-- url     : https://prove2.me/submissions/245f578d-a7e6-49e3-b46c-2887dc98290d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (f : ℕ → Ω → (ℝ≥0 × ℝ)) (hf : ∀ n, Measurable (f n))
    (hEnum : ∀ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
      Measure.sum (fun n => (A n).indicator (fun _ => Measure.dirac (f n ω)) ω)) :
    ∃ κ : Kernel Ω (ℝ≥0 × ℝ), IsSFiniteKernel κ ∧
      ∀ ω, κ ω =
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by
  classical
  let k : ℕ → Kernel Ω (ℝ≥0 × ℝ) := fun n =>
    Kernel.piecewise (hA n) (Kernel.deterministic (f n) (hf n)) 0
  letI : ∀ n, IsSFiniteKernel (k n) := by
    intro n
    dsimp [k]
    infer_instance
  refine ⟨Kernel.sum k, inferInstance, ?_⟩
  intro ω
  rw [hEnum ω, Kernel.sum_apply]
  congr 1
