-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_finite_mesh_signed_split_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:01:16.288965+00:00
-- url     : https://prove2.me/submissions/0a95c1f7-a341-40e7-92b8-19d11241797f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_dominated_centered_and_nonpositive_mesh_limits
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_mesh_pathwise_signed_upper_bound_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical

/-- A finite-mesh stopped BV budget with true centred source-jump terms and
nonpositive HJB terms supplies the signed M/B witness after dominated passage. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (K : ℝ)
    (Mmesh Bmesh : ℕ → Ω → ℝ) (M B DM DB : Ω → ℝ)
    (hMMeas : ∀ n, AEStronglyMeasurable (Mmesh n) P)
    (hBMeas : ∀ n, AEStronglyMeasurable (Bmesh n) P)
    (hDM : Integrable DM P) (hDB : Integrable DB P)
    (hMDom : ∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω)
    (hBDom : ∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω)
    (hMLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω)))
    (hMMean : ∀ n, (∫ ω, Mmesh n ω ∂P) = 0)
    (hBMean : ∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0)
    (hMesh : ∀ᵐ ω ∂P, ∀ n,
      Y ω ≤ K + Mmesh n ω + Bmesh n ω) :
    ∃ M' B' : Ω → ℝ,
      (Integrable M' P ∧ (∫ ω, M' ω ∂P) = 0) ∧
      (Integrable B' P ∧ (∫ ω, B' ω ∂P) ≤ 0) ∧
      (∀ᵐ ω ∂P, Y ω ≤ K + M' ω + B' ω) := by
  obtain ⟨⟨hMI, hM0⟩, ⟨hBI, hBnonpos⟩⟩ :=
    avram_p3_bv_dominated_centered_and_nonpositive_mesh_limits
      P Mmesh Bmesh M B DM DB hMMeas hBMeas hDM hDB
      hMDom hBDom hMLim hBLim hMMean hBMean
  have hPath :=
    avram_p3_bv_original_mesh_pathwise_signed_upper_bound_limit
      P Y M B Mmesh Bmesh K hMesh hMLim hBLim
  exact ⟨M, B, ⟨hMI, hM0⟩, ⟨hBI, hBnonpos⟩, hPath⟩
