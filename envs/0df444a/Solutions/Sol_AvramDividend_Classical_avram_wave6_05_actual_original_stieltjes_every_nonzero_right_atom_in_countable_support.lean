-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_original_stieltjes_every_nonzero_right_atom_in_countable_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:14:07.838074+00:00
-- url     : https://prove2.me/submissions/c7bba35d-57b4-4543-af3a-94198147db84

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stieltjes_atomic_weighted_tsum_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

/-- The countable atomic support of the actual right-Stieltjes dividend
measure contains every nonzero right-payment atom; no hidden positive-time
or endpoint payment is omitted from its weighted sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      ((∫⁻ s, f s ∂μ) =
        (∫⁻ s, f s ∂μatom) + (∫⁻ s, f s ∂μdiffuse)) ∧
      ((∫⁻ s, f s ∂μatom) =
        ∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) := by
  rcases avram_wave6_05_actual_original_stieltjes_atomic_weighted_tsum_exact
    X x D hD ω T f with
    ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hAtom,
      hOutside, hNull, hAt, hFull, hTsum⟩
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hAtom,
    hOutside, hNull, hAt, hFull, hTsum, ?_⟩
  intro s hMass
  by_contra hNot
  have hSub : ({s} : Set ℝ) ⊆ Aᶜ := by
    intro y hy
    have heq : y = s := Set.mem_singleton_iff.mp hy
    simpa [heq] using hNot
  have hAtomicZero : μatom {s} = 0 :=
    measure_mono_null hSub hOutside
  letI : NullSingletonClass μdiffuse := hNull
  have hDiffuseZero : μdiffuse {s} = 0 := measure_singleton s
  apply hMass
  rw [hSplit]
  simp [hAtomicZero, hDiffuseZero]
