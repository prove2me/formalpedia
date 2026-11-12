-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja24_original_marked_strip_second_moment_of_L2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:36:39.433279+00:00
-- url     : https://prove2.me/submissions/06679231-ebcd-4ab1-83c7-c47037ac2907
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja27_marked_simple_energy_dominated_limit
import Theorems.Thm_AvramDividend_Classical_avram_ja28_original_borel_mark_simple_energy_certificate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- The source physical Borel partition certificate and the proved dominated
energy transfer yield the exact original marked strip quadratic moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let C : Ω → ℝ := fun ω =>
        (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) -
          (t : ℝ) * (∫ z in S, z ∂X.ν)
      Integrable (fun ω => (C ω) ^ 2) P →
      (∫ ω, (C ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν) := by
  intro n m hnm t S NX C hSq
  have hPhysical :=
    avram_ja28_original_borel_mark_simple_energy_certificate
      X hX hFinite n m hnm t
  obtain ⟨K, B, c, g, hCell, hDisj,
    hMeas, hg, hDom, hLim, hSqMom, hEnergy⟩ := hPhysical
  let F : ℕ → Ω → ℝ := fun k ω =>
    ∑ i ∈ Finset.range (K k),
      c k i * ((NX ω (Ioc 0 t ×ˢ B k i)).toReal -
        (((t : ℝ≥0∞) * X.ν (B k i)).toReal))
  let E : ℕ → ℝ := fun k =>
    ∑ i ∈ Finset.range (K k),
      (c k i) ^ 2 * (((t : ℝ≥0∞) * X.ν (B k i)).toReal)
  exact avram_ja27_marked_simple_energy_dominated_limit
    F C g E ((t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν))
    hMeas hg hDom hLim hSqMom hEnergy
