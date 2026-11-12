-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_iid_full_stream_deterministic_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:37:17.059259+00:00
-- url     : https://prove2.me/submissions/27a37b14-9a73-497b-8a0a-770fb4e4ed06

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section
/-- Reindexing an independent identically distributed real sequence leaves
    its complete infinite-stream law unchanged. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hiid : iIndepFun τ P)
    (μ : Measure ℝ)
    (hLaw : ∀ n, HasLaw (τ n) μ P)
    (m : ℕ) :
    IdentDistrib (fun ω (j : ℕ) => τ (m + j) ω)
      (fun ω (j : ℕ) => τ j ω) P P := by
  have htail : iIndepFun (fun j ω => τ (m + j) ω) P := by
    have h' := hiid.precomp (g := fun j : ℕ => m + j)
      (by intro i j h; exact Nat.add_left_cancel h)
    simpa [Function.comp] using h'
  have htailLaw (j : ℕ) : HasLaw (fun ω => τ (m + j) ω) μ P :=
    hLaw (m + j)
  have htailAE : AEMeasurable (fun ω (j : ℕ) => τ (m + j) ω) P :=
    (aemeasurable_pi_iff).2 (fun j => (htailLaw j).aemeasurable)
  have horigAE : AEMeasurable (fun ω (j : ℕ) => τ j ω) P :=
    (aemeasurable_pi_iff).2 (fun j => (hLaw j).aemeasurable)
  have h1 : HasLaw (fun ω (j : ℕ) => τ (m + j) ω)
      (Measure.infinitePi (fun _ : ℕ => μ)) P :=
    htail.hasLaw_infinitePi htailLaw htailAE
  have h2 : HasLaw (fun ω (j : ℕ) => τ j ω)
      (Measure.infinitePi (fun _ : ℕ => μ)) P :=
    hiid.hasLaw_infinitePi hLaw horigAE
  exact h1.identDistrib h2