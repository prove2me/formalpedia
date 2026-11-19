-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward79_two_stage_cutoff_mesh_signed_L1_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:00:41.253444+00:00
-- url     : https://prove2.me/submissions/25397a28-5982-4f1b-bfd6-9311db047900

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward78_L1_vanishing_signed_mesh_error_select
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F K : Ω → ℝ) (E R : ℕ → Ω → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hKI : Integrable K P)
    (hKSmall : (∫ ω, |K ω| ∂P) ≤ ε / 2)
    (hEI : ∀ k, Integrable (E k) P)
    (hR : ∀ k, ∀ᵐ ω ∂P, R k ω ≤ 0)
    (hLedger : ∀ k, ∀ᵐ ω ∂P,
      F ω ≤ K ω + E k ω + R k ω)
    (hVan : Tendsto (fun k => ∫ ω, |E k ω| ∂P)
      Filter.atTop (𝓝 (0 : ℝ))) :
    ∃ e r : Ω → ℝ,
      Integrable e P ∧
      (∫ ω, |e ω| ∂P) ≤ ε ∧
      (∀ᵐ ω ∂P, r ω ≤ 0) ∧
      (∀ᵐ ω ∂P, F ω ≤ e ω + r ω) := by
  have hLedger' (k : ℕ) :
      ∀ᵐ ω ∂P, F ω - K ω ≤ E k ω + R k ω := by
    filter_upwards [hLedger k] with ω hh
    linarith
  have hHalf : 0 < ε / 2 := by linarith
  obtain ⟨e', r, heI, heSmall, hr, hbound⟩ :=
    AvramDividend.Classical.avram_pj_reward78_L1_vanishing_signed_mesh_error_select
      P (fun ω => F ω - K ω) E R hEI hR hLedger' hVan
      (ε / 2) hHalf
  refine ⟨fun ω => K ω + e' ω, r, hKI.add heI, ?_, hr, ?_⟩
  · have hAbsI : Integrable (fun ω => |K ω + e' ω|) P :=
      (hKI.add heI).abs
    have hSumI : Integrable (fun ω => |K ω| + |e' ω|) P :=
      hKI.abs.add heI.abs
    have hAbsLe :
        (∫ ω, |K ω + e' ω| ∂P) ≤
        (∫ ω, |K ω| + |e' ω| ∂P) :=
      integral_mono_ae hAbsI hSumI
        (Filter.Eventually.of_forall (fun ω => abs_add_le (K ω) (e' ω)))
    rw [integral_add hKI.abs heI.abs] at hAbsLe
    linarith
  · filter_upwards [hbound] with ω hh
    linarith
