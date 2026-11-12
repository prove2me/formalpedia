-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_marked_band_random_index_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:42:55.946872+00:00
-- url     : https://prove2.me/submissions/f9040345-7be3-4595-8ee4-25253f7aa058

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_vector_mark_independent
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_mark_stream_shift_identDistrib
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
import Theorems.Thm_AvramDividend_Classical_avram_a06_generic_indep_pair_random_Ico_mark_shift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Original count-pair independence and full mark-stream shift invariance give
    the stopped original finite-band mark law. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s k : ℝ≥0) :
    IdentDistrib
      (fun ω => ∑ j ∈ Finset.Ico (LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (s : ℝ))
        (LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (s + k : ℝ)), Y j ω)
      (fun ω => ∑ j ∈ Finset.range
        ((LevyFoundations.jumpCount
          (fun j => LevyFoundations.arrival τ j ω) (s + k : ℝ)) -
          (LevyFoundations.jumpCount
          (fun j => LevyFoundations.arrival τ j ω) (s : ℝ))), Y j ω) P P := by
  let t : Fin 2 → ℝ≥0 := fun i => if i = 0 then s else s + k
  let N : ((ℕ → ℝ) × (ℕ → ℝ)) → Fin 2 → ℕ :=
    fun ω i => LevyFoundations.jumpCount
      (fun j => LevyFoundations.arrival τ j ω) (t i : ℝ)
  let M : ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ → ℝ := fun ω j => Y j ω
  have hN : Measurable N := by
    refine measurable_pi_iff.2 ?_
    intro i
    exact AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public
      τ hd.measurable_interarrival (t i : ℝ)
  have hM : AEMeasurable M P :=
    (aemeasurable_pi_iff).2 (fun j => (hd.law_mark j).aemeasurable)
  have hNM : IndepFun N M P := by
    exact AvramDividend.Classical.avram_a06_original_cp_count_vector_mark_independent
      P τ Y hd 2 t
  have hshift (m : ℕ) : IdentDistrib (fun ω j => M ω (m + j)) M P P :=
    AvramDividend.Classical.avram_a06_original_cp_mark_stream_shift_identDistrib
      P τ Y hd m
  have hdist :=
    AvramDividend.Classical.avram_a06_generic_indep_pair_random_Ico_mark_shift
      P N M hN.aemeasurable hM hNM hshift
  simpa [N, M, t] using hdist
