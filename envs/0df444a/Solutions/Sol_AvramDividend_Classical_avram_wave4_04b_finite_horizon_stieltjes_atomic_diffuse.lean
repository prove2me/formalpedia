-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:35:48.220149+00:00
-- url     : https://prove2.me/submissions/8c2b0073-ccab-483c-9372-2056643f031d

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_exists_atomic_diffuse_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
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
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) := by
  dsimp only
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  have hMass : μ Set.univ = ENNReal.ofReal (rightLimit D T ω) := by
    calc
      μ Set.univ = (dividendMeasure D ω) (Icc (0 : ℝ) (T : ℝ)) := by
        simp [μ]
      _ = ENNReal.ofReal (rightLimit D T ω) :=
        avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
  letI : IsFiniteMeasure μ := ⟨by
    rw [hMass]
    exact ENNReal.ofReal_lt_top⟩
  obtain ⟨A, μatom, μdiffuse, hAcount, hAmeas, hdecomp, hsum, hsupport, hnull⟩ :=
    BookProof.ChapterMeasureAtomicDiffuse.exists_atomic_diffuse_decomposition μ
  have hSingleton (t : ℝ≥0) (ht : t ≤ T) :
      μ {(t : ℝ)} =
        ENNReal.ofReal (rightLimit D t ω - D t ω) := by
    have hmem : (t : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) := by
      constructor
      · exact t.property
      · exact_mod_cast ht
    calc
      μ {(t : ℝ)} = (dividendMeasure D ω) {(t : ℝ)} := by
        simp [μ, hmem]
      _ = ENNReal.ofReal (rightLimit D t ω - D t ω) :=
        dividendMeasure_singleton_eq_rightLimit_sub D hD ω t
  exact ⟨A, μatom, μdiffuse, hAcount, hAmeas, hdecomp,
    hsum, hsupport, hnull, hSingleton, hMass⟩
