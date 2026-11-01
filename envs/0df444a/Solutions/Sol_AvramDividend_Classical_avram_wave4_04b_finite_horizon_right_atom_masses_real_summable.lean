-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_finite_horizon_right_atom_masses_real_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:52:09.489096+00:00
-- url     : https://prove2.me/submissions/ab986e06-a54f-4915-8c63-d2d11e48e5cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- The actual full finite-horizon Stieltjes dividend mass controls the
countable real sum of all right-payment atom masses, while the genuine
atomless remainder is retained for singular-continuous variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      Summable (fun t : A => (μ {(t : ℝ)}).toReal) ∧
      (∑' t : A, μ {(t : ℝ)}) ≤
        ENNReal.ofReal (rightLimit D T ω) := by
  dsimp only
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  obtain ⟨A, μatom, μdiffuse, hAcount, hAmeas, hdecomp,
    hsum, hsupport, hnull, hsingle, hMass⟩ :=
    avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse D hD ω T
  have hAtomSum :
      μatom Set.univ = (∑' t : A, μ {(t : ℝ)}) := by
    calc
      μatom Set.univ =
          (∫⁻ s : ℝ, (1 : ℝ≥0∞) ∂μatom) := by simp
      _ = (∑' t : A, μ {(t : ℝ)}) := by
        rw [hsum, lintegral_sum_measure]
        apply tsum_congr
        intro t
        rw [lintegral_smul_measure, lintegral_dirac]
        simp [μ]
  have hAtomBound : μatom Set.univ ≤ μ Set.univ := by
    have hEval : μ Set.univ = (μatom + μdiffuse) Set.univ :=
      congrArg (fun ν : Measure ℝ => ν Set.univ) hdecomp
    calc
      μatom Set.univ ≤ (μatom + μdiffuse) Set.univ := by
        rw [Measure.add_apply]
        exact le_add_right (le_refl _)
      _ = μ Set.univ := hEval.symm
  have hTotalFinite : μ Set.univ < (⊤ : ℝ≥0∞) := by
    rw [hMass]
    exact ENNReal.ofReal_lt_top
  have hTsumFinite :
      (∑' t : A, μ {(t : ℝ)}) ≠ (⊤ : ℝ≥0∞) := by
    rw [← hAtomSum]
    exact ne_top_of_lt (lt_of_le_of_lt hAtomBound hTotalFinite)
  have hRealSummable :
      Summable (fun t : A => (μ {(t : ℝ)}).toReal) :=
    ENNReal.summable_toReal hTsumFinite
  refine ⟨A, μatom, μdiffuse, hAcount, hAmeas, hdecomp,
    hsum, hsupport, hnull, hRealSummable, ?_⟩
  calc
    (∑' t : A, μ {(t : ℝ)}) = μatom Set.univ := hAtomSum.symm
    _ ≤ μ Set.univ := hAtomBound
    _ = ENNReal.ofReal (rightLimit D T ω) := hMass
