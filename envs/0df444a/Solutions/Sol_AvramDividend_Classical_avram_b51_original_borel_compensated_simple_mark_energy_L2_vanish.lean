-- Prove2me | solution 1 for AvramDividend.Classical.avram_b51_original_borel_compensated_simple_mark_energy_L2_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:13:23.574567+00:00
-- url     : https://prove2.me/submissions/fa498a77-1355-490f-bec7-827f05551392

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_finite_borel_mark_source_isometry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original compensated marked Borel simple processes have square expectation vanishing with physical energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (K : ℕ → ℕ)
    (B : ℕ → ℕ → Set ℝ) (c : ℕ → ℕ → ℝ)
    (hB : ∀ n i, i ∈ Finset.range (K n) →
      MeasurableSet (B n i))
    (hNeg : ∀ n i, i ∈ Finset.range (K n) →
      B n i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ n i j, i ∈ Finset.range (K n) →
      j ∈ Finset.range (K n) → i ≠ j →
      Disjoint (B n i) (B n j))
    (hEnergy : Tendsto
      (fun n => ∑ i ∈ Finset.range (K n),
        (c n i)^2 * ((t : ℝ≥0∞) * X.ν (B n i)).toReal)
      atTop (𝓝 (0 : ℝ))) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∃ F : ℕ → Ω → ℝ,
      (∀ n ω, F n ω = ∑ i ∈ Finset.range (K n),
        c n i * ((NX ω (Ioc 0 t ×ˢ B n i)).toReal -
          ((t : ℝ≥0∞) * X.ν (B n i)).toReal)) ∧
      Tendsto (fun n => ∫ ω, (F n ω)^2 ∂P)
        atTop (𝓝 (0 : ℝ)) := by 
  classical
  dsimp only
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let F : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range (K n),
    c n i * ((NX ω (Ioc 0 t ×ˢ B n i)).toReal -
      ((t : ℝ≥0∞) * X.ν (B n i)).toReal)
  refine ⟨F, ?_, ?_⟩
  · intro n ω
    rfl
  have hEq (n : ℕ) :
      (∫ ω, (F n ω)^2 ∂P) =
        ∑ i ∈ Finset.range (K n),
          (c n i)^2 * ((t : ℝ≥0∞) * X.ν (B n i)).toReal := by
    exact (avram_ja31_original_finite_borel_mark_source_isometry
      X hFinite t (Finset.range (K n)) (B n) (c n)
      (hB n) (hNeg n)
      (fun i hi j hj hij => hDisj n i j hi hj hij)).2
  have hFun :
      (fun n => ∫ ω, (F n ω)^2 ∂P) =
      (fun n => ∑ i ∈ Finset.range (K n),
        (c n i)^2 * ((t : ℝ≥0∞) * X.ν (B n i)).toReal) := by
    funext n
    exact hEq n
  rw [hFun]
  exact hEnergy
