-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_simple_mark_fibre_centered_energy_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:00:33.125223+00:00
-- url     : https://prove2.me/submissions/6757a444-38db-48e2-b013-2d9b2716c664

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_disjoint_borel_weighted_centered_energy_20261112
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal BigOperators
noncomputable section

/-- Exact physical Poisson energy for measurable disjoint fibres of a bounded
finite-range Borel mark (boundedness follows from finite range). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hNeg : S ⊆ Iio (0 : ℝ))
    (g : SimpleFunc ℝ ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let r : ℝ → ℝ := fun y => ((T : ℝ≥0∞) * X.ν (B y)).toReal
    let F : Ω → ℝ := fun ω =>
      ∑ y ∈ g.range, y * ((NX ω (Ioc 0 T ×ˢ B y)).toReal - r y)
    let E : ℝ := ∑ y ∈ g.range, y ^ 2 * r y
    Integrable (fun ω => (F ω) ^ 2) P ∧
      (∫ ω, (F ω) ^ 2 ∂P) = E := by
  classical
  let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
  have hB : ∀ y ∈ g.range, MeasurableSet (B y) := by
    intro y hy
    exact hS.inter ((measurableSet_singleton y).preimage g.measurable)
  have hNegB : ∀ y ∈ g.range, B y ⊆ Iio (0 : ℝ) := by
    intro y hy z hz
    exact hNeg hz.1
  have hDisj : ∀ y ∈ g.range, ∀ v ∈ g.range,
      y ≠ v → Disjoint (B y) (B v) := by
    intro y hy v hv hne
    apply Set.disjoint_left.mpr
    intro z hzy hzv
    exact hne (hzy.2.symm.trans hzv.2)
  simpa only [B, id_eq] using
    (avram_a21_original_disjoint_borel_weighted_centered_energy_20261112
      X hFinite T g.range B id hB hNegB hDisj)
