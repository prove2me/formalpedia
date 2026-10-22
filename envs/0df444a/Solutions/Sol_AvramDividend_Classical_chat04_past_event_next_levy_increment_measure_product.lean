-- Prove2me | solution 1 for AvramDividend.Classical.chat04_past_event_next_levy_increment_measure_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:42:11.223106+00:00
-- url     : https://prove2.me/submissions/c5ba5548-a194-4c28-8ae4-ed8056ac26b7

import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Fundamental event-level finite-prefix extension rule: every event
measurable at u, including the joint event of any number of previous
increments and arbitrary F_s-past restrictions, factors from the next
increment X_v-X_u. This is the induction step for finite-dimensional
independence, obtained exactly from the full-filtration Levy axiom.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u v : ℝ≥0) (huv : u ≤ v)
    (A : Set Ω) (hA : MeasurableSet[𝓕 u] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    P (A ∩ {ω | X.X v ω - X.X u ω ∈ B}) =
      P A * P {ω | X.X v ω - X.X u ω ∈ B} := by
  let g : Ω → ℝ := fun ω => X.X v ω - X.X u ω
  have hg : MeasurableSet[MeasurableSpace.comap g inferInstance]
      (g ⁻¹' B) :=
    hB.preimage (comap_measurable g)
  have hIndep :
      Indep (MeasurableSpace.comap g inferInstance) (𝓕 u) P := by
    simpa only [g] using X.indepIncrements u v huv
  have hProd :=
    (ProbabilityTheory.Indep_iff
      (MeasurableSpace.comap g inferInstance) (𝓕 u) P).mp
      hIndep (g ⁻¹' B) A hg hA
  change P (A ∩ (g ⁻¹' B)) = P A * P (g ⁻¹' B)
  simpa only [Set.inter_comm, mul_comm] using hProd
