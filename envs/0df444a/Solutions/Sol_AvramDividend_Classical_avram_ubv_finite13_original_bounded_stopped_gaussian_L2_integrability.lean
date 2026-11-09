-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite13_original_bounded_stopped_gaussian_L2_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:36:57.147021+00:00
-- url     : https://prove2.me/submissions/037f6eb8-bb6b-4b2b-97c3-65b52d58be43

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_monotone_clock_reindex

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The original zero-jump Gaussian source has square-integrable values at
bounded sampled stopping times; the earlier value is measurable with respect
to its own stopped history, and the two-stopped product is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (grid : ℕ → ℝ≥0) (hgrid : Monotone grid)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (grid i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (hgrid hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (grid i) } : Filtration ℕ mΩ))
    (α β : Ω → WithTop ℕ)
    (hα : IsStoppingTime 𝓖 α) (hβ : IsStoppingTime 𝓖 β)
    (hαβ : α ≤ β)
    (N : ℕ) (hbounded : ∀ ω, β ω ≤ (N : WithTop ℕ)) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
    MemLp (stoppedValue (fun i : ℕ => M (grid i)) α) 2 P ∧
    MemLp (stoppedValue (fun i : ℕ => M (grid i)) β) 2 P ∧
    StronglyMeasurable[hα.measurableSpace]
      (stoppedValue (fun i : ℕ => M (grid i)) α) ∧
    Integrable (fun ω =>
      stoppedValue (fun i : ℕ => M (grid i)) α ω *
      stoppedValue (fun i : ℕ => M (grid i)) β ω) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
  let Q : ℝ≥0 → Ω → ℝ := fun t ω => (M t ω)^2 - (t : ℝ) * X.σ^2
  change MemLp (stoppedValue (fun i : ℕ => M (grid i)) α) 2 P ∧
    MemLp (stoppedValue (fun i : ℕ => M (grid i)) β) 2 P ∧
    StronglyMeasurable[hα.measurableSpace]
      (stoppedValue (fun i : ℕ => M (grid i)) α) ∧
    Integrable (fun ω =>
      stoppedValue (fun i : ℕ => M (grid i)) α ω *
      stoppedValue (fun i : ℕ => M (grid i)) β ω) P
  have hm : Martingale (fun i : ℕ => M (grid i)) 𝓖 P := by
    rw [h𝓖]
    exact chat03_martingale_monotone_clock_reindex M
      (avram_wave6_03_original_rightCont_zerojump_centered_source_martingale X hν)
      grid hgrid
  have hq : Martingale (fun i : ℕ => Q (grid i)) 𝓖 P := by
    rw [h𝓖]
    exact chat03_martingale_monotone_clock_reindex Q
      (avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale X hν)
      grid hgrid
  have hsq (i : ℕ) : Integrable (fun ω => (M (grid i) ω)^2) P := by
    have hraw : Integrable
        (fun ω => Q (grid i) ω + (grid i : ℝ) * X.σ^2) P := by
      convert (hq.integrable i).add
        (integrable_const ((grid i : ℝ) * X.σ^2)) using 1 <;> rfl
    have heq : (fun ω => Q (grid i) ω + (grid i : ℝ) * X.σ^2) =
        (fun ω => (M (grid i) ω)^2) := by
      funext ω
      dsimp [Q]
      ring
    rw [heq] at hraw
    exact hraw
  have hLp (i : ℕ) : MemLp (M (grid i)) 2 P :=
    (memLp_two_iff_integrable_sq (hm.integrable i).aestronglyMeasurable).2 (hsq i)
  have hαLp : MemLp (stoppedValue (fun i : ℕ => M (grid i)) α) 2 P :=
    memLp_stoppedValue hα hLp (fun ω => le_trans (hαβ ω) (hbounded ω))
  have hβLp : MemLp (stoppedValue (fun i : ℕ => M (grid i)) β) 2 P :=
    memLp_stoppedValue hβ hLp hbounded
  refine ⟨hαLp, hβLp, ?_, ?_⟩
  · exact (measurable_stoppedValue
      hm.stronglyAdapted.isStronglyProgressive_of_discrete hα).stronglyMeasurable
  · convert MemLp.integrable_mul hαLp hβLp using 1 <;> rfl
