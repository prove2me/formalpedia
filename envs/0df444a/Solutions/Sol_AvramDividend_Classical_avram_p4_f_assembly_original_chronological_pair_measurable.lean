-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:57:12.850801+00:00
-- url     : https://prove2.me/submissions/41f1e5b2-1445-42fe-b227-b6979494ae1c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_factorial_pair_identity
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Measurability of the chronological pair count follows from the actual marked jump count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    Measurable (fun ω : Ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)) := by
  classical
  dsimp only
  let F : Ω → Finset ℝ≥0 := fun ω =>
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let J : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
  let K : Ω → ℝ≥0∞ := fun ω =>
    ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)
  have hJmeas : Measurable J := by
    exact avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X 0 T (by exact zero_le) _ measurableSet_Iic
  have hpair (ω : Ω) :
      ((F ω).card * ((F ω).card - 1)) / 2 =
        ((F ω ×ˢ F ω).filter
          (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by
    exact (avram_p4_f_assembly_original_negative_band_factorial_pair_identity X ω T n).2
  have hJcast (ω : Ω) : J ω = ((F ω).card : ℝ≥0∞) := by
    exact (avram_p4_f_assembly_original_negative_band_factorial_pair_identity X ω T n).1
  have hCastMeas : Measurable (fun ω : Ω => ((F ω).card : ℝ≥0∞)) := by
    have hfun : (fun ω : Ω => ((F ω).card : ℝ≥0∞)) = J := by
      funext ω
      exact (hJcast ω).symm
    rw [hfun]
    exact hJmeas
  have hEmb : MeasurableEmbedding (Nat.cast : ℕ → ℝ≥0∞) :=
    MeasurableEmbedding.natCast
  have hNmeas : Measurable (fun ω : Ω => (F ω).card) :=
    hEmb.measurable_comp_iff.mp hCastMeas
  have hFunc : Measurable (fun j : ℕ => (((j * (j - 1)) / 2 : ℕ) : ℝ≥0∞)) :=
    measurable_of_countable _
  have hvia : Measurable (fun ω : Ω =>
      (((((F ω).card * ((F ω).card - 1)) / 2 : ℕ) : ℝ≥0∞))) :=
    hFunc.comp hNmeas
  have hEq : K = (fun ω : Ω =>
      (((((F ω).card * ((F ω).card - 1)) / 2 : ℕ) : ℝ≥0∞))) := by
    funext ω
    exact congrArg (fun j : ℕ => (j : ℝ≥0∞)) (hpair ω).symm
  change Measurable K
  rw [hEq]
  exact hvia
