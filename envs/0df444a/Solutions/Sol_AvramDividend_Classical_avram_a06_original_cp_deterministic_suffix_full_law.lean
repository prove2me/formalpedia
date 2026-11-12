-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_deterministic_suffix_full_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:20:51.214021+00:00
-- url     : https://prove2.me/submissions/c1c7fbb8-aaab-47fd-954c-f1ea06282e1c

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Every deterministic suffix of the original rate-one compound-Poisson
    interarrival stream has the full infinite product exponential law. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (n : ℕ) :
    HasLaw (fun ω (j : ℕ) => τ (n + j) ω)
      (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))) P := by
  have hiid : iIndepFun τ P := by
    have h' := hd.indep.precomp (g := Sum.inl) Sum.inl_injective
    simpa [Function.comp] using h'
  have hTail : iIndepFun (fun j ω => τ (n + j) ω) P := by
    have h' := hiid.precomp (g := fun j : ℕ => n + j)
      (by intro i j h; exact Nat.add_left_cancel h)
    simpa [Function.comp] using h'
  have hLaw (j : ℕ) :
      HasLaw (τ (n + j)) (expMeasure (1 : ℝ)) P :=
    hd.law_interarrival (n + j)
  exact hTail.hasLaw_infinitePi hLaw
    ((aemeasurable_pi_iff).2 (fun j => (hLaw j).aemeasurable))
