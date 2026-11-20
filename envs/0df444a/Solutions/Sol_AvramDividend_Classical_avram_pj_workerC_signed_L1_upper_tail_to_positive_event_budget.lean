-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_signed_L1_upper_tail_to_positive_event_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:50:36.167183+00:00
-- url     : https://prove2.me/submissions/d3e438a9-2883-4804-8d26-3d2e219633d0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward71_original_posresidual_signed_ledger_transfer
open MeasureTheory Set Filter Topology
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : Set Ω) (G U K : Ω → ℝ) (E Q : ℕ → Ω → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hGU : Integrable (fun ω => G ω - U ω) P)
    (hKI : Integrable K P)
    (hKsmall : (∫ ω, |K ω| ∂P) ≤ ε / 4)
    (hEI : ∀ k, Integrable (E k) P)
    (hQ : ∀ k, ∀ᵐ ω ∂P, Q k ω ≤ 0)
    (hBound : ∀ k, ∀ᵐ ω ∂P,
      G ω - U ω ≤ K ω + E k ω + Q k ω)
    (hVan : Tendsto (fun k => ∫ ω, |E k ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    (∫ ω in A, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε / 2 := by
  have hsmall : (0 : ℝ) < ε / 4 := by linarith [hε]
  have hevent : ∀ᶠ k in Filter.atTop,
      (∫ ω, |E k ω| ∂P) < ε / 4 :=
    (tendsto_order.1 hVan).2 _ hsmall
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hevent
  have hKabs : Integrable (fun ω => |K ω|) P := hKI.abs
  have hEabs : Integrable (fun ω => |E k ω|) P := (hEI k).abs
  have hSumI : Integrable (fun ω => K ω + E k ω) P :=
    hKI.add (hEI k)
  have hIntegralBound :
      (∫ ω, |K ω + E k ω| ∂P) ≤ ε / 2 := by
    have hTriangle :
        (∫ ω, |K ω + E k ω| ∂P) ≤
          ∫ ω, |K ω| + |E k ω| ∂P :=
      integral_mono hSumI.abs (hKabs.add hEabs)
        (fun ω => abs_add_le (K ω) (E k ω))
    rw [integral_add hKabs hEabs] at hTriangle
    linarith [hKsmall, hk k le_rfl]
  exact AvramDividend.Classical.avram_pj_reward71_original_posresidual_signed_ledger_transfer
    A G U (fun ω => K ω + E k ω) (Q k) (ε / 2)
    hGU hSumI
    (by filter_upwards [hBound k] with ω h
        simpa only [add_assoc] using h)
    (hQ k) hIntegralBound
