-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_mark_stream_shift_identDistrib
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T02:41:13.141323+00:00
-- url     : https://prove2.me/submissions/a07ce845-6096-4926-81e3-85f04da81f0d

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Every deterministic tail of the original iid mark stream has the full mark-stream law. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (m : ℕ) :
    IdentDistrib (fun ω (j : ℕ) => Y (m + j) ω)
      (fun ω (j : ℕ) => Y j ω) P P := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)
  have hm : ν Set.univ = 1 :=
    AvramDividend.Classical.avram_a06_uniform_negative_mark_measure_facts.2.1
  letI : IsProbabilityMeasure ν := ⟨hm⟩
  have hmark : iIndepFun Y P := by
    have h' := hd.indep.precomp (g := Sum.inr) Sum.inr_injective
    simpa [Function.comp] using h'
  have htail : iIndepFun (fun j ω => Y (m + j) ω) P := by
    have h' := hmark.precomp (g := fun j : ℕ => m + j)
      (by intro i j h; exact Nat.add_left_cancel h)
    simpa [Function.comp] using h'
  have htailLaw (j : ℕ) : HasLaw (fun ω => Y (m + j) ω) ν P :=
    hd.law_mark (m + j)
  have hmarkLaw (j : ℕ) : HasLaw (Y j) ν P := hd.law_mark j
  have htailAE : AEMeasurable (fun ω (j : ℕ) => Y (m + j) ω) P :=
    (aemeasurable_pi_iff).2 (fun j => (htailLaw j).aemeasurable)
  have hmarkAE : AEMeasurable (fun ω (j : ℕ) => Y j ω) P :=
    (aemeasurable_pi_iff).2 (fun j => (hmarkLaw j).aemeasurable)
  have h1 : HasLaw (fun ω (j : ℕ) => Y (m + j) ω)
      (Measure.infinitePi (fun _ : ℕ => ν)) P :=
    htail.hasLaw_infinitePi htailLaw htailAE
  have h2 : HasLaw (fun ω (j : ℕ) => Y j ω)
      (Measure.infinitePi (fun _ : ℕ => ν)) P :=
    hmark.hasLaw_infinitePi hmarkLaw hmarkAE
  exact h1.identDistrib h2
