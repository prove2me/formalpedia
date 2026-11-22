-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_abstract_integrable_charged_mesh_L1_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T09:21:02.061392+00:00
-- url     : https://prove2.me/submissions/042519c0-c144-4694-8f2a-668a12a6543e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_lsc_abstract_charged_mesh_L1_to_expected_positive_budget
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A charged source with an integrable true stopped cash balance and
integrable Gaussian mesh has the expected cofinal finite-band budget. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (F N Occ : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (B c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hFBI : IntegrableOn
      (fun ω => F ω - (B + c * Occ ω)) A P)
    (hNI : IntegrableOn N A P)
    (hMInt : ∀ m, IntegrableOn (M m) A P)
    (hL1 : Tendsto (fun m =>
      ∫ ω in A, |N ω - M m ω| ∂P) atTop (𝓝 (0 : ℝ)))
    (hR : Tendsto (fun m =>
      ∫ ω in A, max (F ω - M m ω - (B + c * Occ ω)) 0 ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hFI : ∀ m, IntegrableOn (fun ω => max (F ω - M m ω) 0) A P)
    (hOccI : IntegrableOn Occ A P)
    (hOccNonneg : ∀ᵐ ω ∂(P.restrict A), 0 ≤ Occ ω) :
    ∀ ε : ℝ, 0 < ε → ∀ K : ℕ, ∃ m : ℕ, K < m ∧
      (∫ ω in A, max (F ω - M m ω) 0 ∂P) ≤
        B + c * (∫ ω in A, Occ ω ∂P) + ε := by
  have hInt (S : Ω → ℝ) (hS : IntegrableOn S A P) :
      Integrable (fun ω => F ω - S ω -
        (B + c * Occ ω)) (P.restrict A) := by
    have hBase : Integrable
        (fun ω => (F ω - (B + c * Occ ω)) - S ω) (P.restrict A) :=
      hFBI.sub hS
    have heq : (fun ω => F ω - S ω - (B + c * Occ ω)) =
        (fun ω => (F ω - (B + c * Occ ω)) - S ω) := by
      funext ω
      ring
    rw [heq]
    exact hBase
  have hPos (S : Ω → ℝ) (hS : IntegrableOn S A P) :
      IntegrableOn (fun ω => max (S ω) 0) A P := by
    have hRep : IntegrableOn
        (fun ω => (1 / 2 : ℝ) * (S ω + |S ω|)) A P :=
      (hS.add hS.abs).const_mul (1 / 2 : ℝ)
    convert hRep using 1
    ext ω
    rcases le_total 0 (S ω) with hs | hs
    · rw [max_eq_left hs, abs_of_nonneg hs]
      ring
    · rw [max_eq_right hs, abs_of_nonpos hs]
      ring
  have hI : IntegrableOn
      (fun ω => max (F ω - N ω - (B + c * Occ ω)) 0) A P :=
    hPos (fun ω => F ω - N ω - (B + c * Occ ω)) (hInt N hNI)
  have hMI (m : ℕ) : IntegrableOn
      (fun ω => max (F ω - M m ω - (B + c * Occ ω)) 0) A P :=
    hPos (fun ω => F ω - M m ω - (B + c * Occ ω)) (hInt (M m) (hMInt m))
  have hDI (m : ℕ) :
      IntegrableOn (fun ω => |N ω - M m ω|) A P :=
    (hNI.sub (hMInt m)).abs
  exact avram_lsc_abstract_charged_mesh_L1_to_expected_positive_budget
    P A F N Occ M B c hB hc hI hMI hDI hL1 hR
    hFI hOccI hOccNonneg

