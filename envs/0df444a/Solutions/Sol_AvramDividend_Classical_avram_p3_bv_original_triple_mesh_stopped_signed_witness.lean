-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_triple_mesh_stopped_signed_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:01:12.043677+00:00
-- url     : https://prove2.me/submissions/ccb80658-b985-4124-8023-cdb850e56ab9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_dominated_centered_and_nonpositive_mesh_limits
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_triple_mesh_signed_budget_ae_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical

/-- Finite-mesh original BV source compensation and stopped reward convergence
assemble into the L¹ signed martingale/HJB witness demanded by verification. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Ymesh Mmesh Bmesh : ℕ → Ω → ℝ)
    (Y M B DM DB : Ω → ℝ) (K : ℝ)
    (hMMeas : ∀ n, AEStronglyMeasurable (Mmesh n) P)
    (hBMeas : ∀ n, AEStronglyMeasurable (Bmesh n) P)
    (hDM : Integrable DM P) (hDB : Integrable DB P)
    (hMDom : ∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω)
    (hBDom : ∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω)
    (hYLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω)))
    (hMLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω)))
    (hMMean : ∀ n, (∫ ω, Mmesh n ω ∂P) = 0)
    (hBMean : ∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0)
    (hMesh : ∀ᵐ ω ∂P, ∀ n,
      Ymesh n ω ≤ K + Mmesh n ω + Bmesh n ω) :
    ∃ M' B' : Ω → ℝ,
      (Integrable M' P ∧ (∫ ω, M' ω ∂P) = 0) ∧
      (Integrable B' P ∧ (∫ ω, B' ω ∂P) ≤ 0) ∧
      (∀ᵐ ω ∂P, Y ω ≤ K + M' ω + B' ω) := by
  obtain ⟨⟨hMI, hM0⟩, ⟨hBI, hBnonpos⟩⟩ :=
    avram_p3_bv_dominated_centered_and_nonpositive_mesh_limits
      P Mmesh Bmesh M B DM DB hMMeas hBMeas hDM hDB
      hMDom hBDom hMLim hBLim hMMean hBMean
  have hPath :=
    avram_p3_bv_original_triple_mesh_signed_budget_ae_limit
      P Ymesh Mmesh Bmesh Y M B K hMesh hYLim hMLim hBLim
  exact ⟨M, B, ⟨hMI, hM0⟩, ⟨hBI, hBnonpos⟩, hPath⟩
