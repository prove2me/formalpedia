-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_integrable_cross_split_yields_three_error_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:51:07.521292+00:00
-- url     : https://prove2.me/submissions/ce32b451-13cc-4555-a35a-99f36fd775bc

import Theorems.Thm_AvramDividend_Classical_avram_ga_nonnegative_L1_convergence_persists_on_restriction
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (E B : ℕ → Ω → ℝ)
    (hEI : ∀ m, Integrable (fun ω => max (E m ω) 0) (P.restrict A))
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hTI : ∀ m, Integrable (fun ω => max (E m ω - B m ω) 0)
      (P.restrict A))
    (hTt : Tendsto (fun m => ∫ ω in A, max (E m ω - B m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hBt : Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (nhds (0 : ℝ))) :
    ∃ (T H R : ℕ → Ω → ℝ),
      (∀ m, Integrable (fun ω => max (E m ω) 0) (P.restrict A)) ∧
      (∀ m, Integrable (fun ω => max (T m ω) 0) (P.restrict A)) ∧
      (∀ m, Integrable (fun ω => |H m ω|) (P.restrict A)) ∧
      (∀ m, Integrable (fun ω => max (R m ω) 0) (P.restrict A)) ∧
      (∀ m, ∀ᵐ ω ∂(P.restrict A),
        max (E m ω) 0 ≤
          max (T m ω) 0 + |H m ω| + max (R m ω) 0) ∧
      Tendsto (fun m => ∫ ω in A, max (T m ω) 0 ∂P)
        atTop (nhds (0 : ℝ)) ∧
      Tendsto (fun m => ∫ ω in A, |H m ω| ∂P)
        atTop (nhds (0 : ℝ)) ∧
      Tendsto (fun m => ∫ ω in A, max (R m ω) 0 ∂P)
        atTop (nhds (0 : ℝ))  := by
  let T : ℕ → Ω → ℝ := fun m ω => max (E m ω - B m ω) 0
  let R : ℕ → Ω → ℝ := fun _ _ => 0
  have hTA (m : ℕ) :
      Integrable (fun ω => max (T m ω) 0) (P.restrict A) := by
    simpa only [T, max_assoc, max_self] using hTI m
  have hBA (m : ℕ) :
      Integrable (fun ω => |B m ω|) (P.restrict A) :=
    (hBI m).integrableOn
  have hRA (m : ℕ) :
      Integrable (fun ω => max (R m ω) 0) (P.restrict A) := by
    simp [R]
  have hPoint (m : ℕ) (ω : Ω) :
      max (E m ω) 0 ≤
        max (T m ω) 0 + |B m ω| + max (R m ω) 0 := by
    have h1 : E m ω - B m ω ≤ max (E m ω - B m ω) 0 :=
      le_max_left _ _
    have h2 : B m ω ≤ |B m ω| := le_abs_self _
    have h3 : (0 : ℝ) ≤ max (E m ω - B m ω) 0 :=
      le_max_right _ _
    have h4 : (0 : ℝ) ≤ |B m ω| := abs_nonneg _
    have hmain : max (E m ω) 0 ≤
        max (E m ω - B m ω) 0 + |B m ω| := by
      apply max_le
      · linarith
      · linarith
    simpa [T, R, max_assoc] using hmain
  have hTend : Tendsto
      (fun m => ∫ ω in A, max (T m ω) 0 ∂P)
        atTop (nhds (0 : ℝ)) := by
    simpa only [T, max_assoc, max_self] using hTt
  have hBend : Tendsto (fun m => ∫ ω in A, |B m ω| ∂P)
      atTop (nhds (0 : ℝ)) :=
    avram_ga_nonnegative_L1_convergence_persists_on_restriction
      P A (fun m ω => |B m ω|) hBI
      (by intro m ω; exact abs_nonneg _) hBt
  have hRend : Tendsto
      (fun m => ∫ ω in A, max (R m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by simp [R]
  exact ⟨T, B, R, hEI, hTA, hBA, hRA,
    (fun m => Filter.Eventually.of_forall (hPoint m)),
    hTend, hBend, hRend⟩
