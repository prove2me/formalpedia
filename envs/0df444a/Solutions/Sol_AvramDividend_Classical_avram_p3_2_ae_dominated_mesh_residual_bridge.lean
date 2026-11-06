-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_ae_dominated_mesh_residual_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:12:22.726286+00:00
-- url     : https://prove2.me/submissions/42760798-e011-49de-9442-101d7d36e0b4

import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
noncomputable section
/-- Dominated original-mesh convergence yields one integrable signed residual with nonpositive mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (K : ℝ) (Y : Ω → ℝ)
    (Ymesh Mmesh Bmesh : ℕ → Ω → ℝ)
    (M B DM DB : Ω → ℝ)
    (hMeasM : ∀ n, AEStronglyMeasurable (Mmesh n) P)
    (hMeasB : ∀ n, AEStronglyMeasurable (Bmesh n) P)
    (hIntDM : Integrable DM P) (hIntDB : Integrable DB P)
    (hDomM : ∀ n, ∀ᵐ ω ∂P, ‖Mmesh n ω‖ ≤ DM ω)
    (hDomB : ∀ n, ∀ᵐ ω ∂P, ‖Bmesh n ω‖ ≤ DB ω)
    (hYlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω)))
    (hMlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω)))
    (hMzero : ∀ n, (∫ ω, Mmesh n ω ∂P) = 0)
    (hBupper : ∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0)
    (hGrid : ∀ᵐ ω ∂P, ∀ n,
      Ymesh n ω ≤ K + Mmesh n ω + Bmesh n ω) :
    ∃ E : Ω → ℝ, Integrable E P ∧
      (∫ ω, E ω ∂P) ≤ 0 ∧
      ∀ᵐ ω ∂P, Y ω ≤ K + E ω := by
  have hMMeas : AEStronglyMeasurable M P :=
    aestronglyMeasurable_of_tendsto_ae atTop hMeasM hMlim
  have hBMeas : AEStronglyMeasurable B P :=
    aestronglyMeasurable_of_tendsto_ae atTop hMeasB hBlim
  have hDomMAll : ∀ᵐ ω ∂P, ∀ n, ‖Mmesh n ω‖ ≤ DM ω :=
    ae_all_iff.mpr hDomM
  have hDomBAll : ∀ᵐ ω ∂P, ∀ n, ‖Bmesh n ω‖ ≤ DB ω :=
    ae_all_iff.mpr hDomB
  have hMBound : ∀ᵐ ω ∂P, ‖M ω‖ ≤ DM ω := by
    filter_upwards [hDomMAll, hMlim] with ω hbd hlim
    exact le_of_tendsto hlim.norm (Filter.Eventually.of_forall hbd)
  have hBBound : ∀ᵐ ω ∂P, ‖B ω‖ ≤ DB ω := by
    filter_upwards [hDomBAll, hBlim] with ω hbd hlim
    exact le_of_tendsto hlim.norm (Filter.Eventually.of_forall hbd)
  have hMInt : Integrable M P := hIntDM.mono' hMMeas hMBound
  have hBInt : Integrable B P := hIntDB.mono' hBMeas hBBound
  have hMIntegral :
      Tendsto (fun n => ∫ ω, Mmesh n ω ∂P) atTop
        (nhds (∫ ω, M ω ∂P)) :=
    tendsto_integral_of_dominated_convergence DM
      hMeasM hIntDM hDomM hMlim
  have hBIntegral :
      Tendsto (fun n => ∫ ω, Bmesh n ω ∂P) atTop
        (nhds (∫ ω, B ω ∂P)) :=
    tendsto_integral_of_dominated_convergence DB
      hMeasB hIntDB hDomB hBlim
  have hMMeanZero : (∫ ω, M ω ∂P) = 0 := by
    have hconst :
        Tendsto (fun n => ∫ ω, Mmesh n ω ∂P) atTop
          (nhds (0 : ℝ)) := by
      simpa only [hMzero] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    exact tendsto_nhds_unique hMIntegral hconst
  have hBMeanUpper : (∫ ω, B ω ∂P) ≤ 0 :=
    le_of_tendsto hBIntegral (Filter.Eventually.of_forall hBupper)
  have hUpper : ∀ᵐ ω ∂P, Y ω ≤ K + M ω + B ω := by
    filter_upwards [hYlim, hMlim, hBlim, hGrid] with ω hy hm hb hbound
    have hsum : Tendsto
        (fun n => K + Mmesh n ω + Bmesh n ω) atTop
        (nhds (K + M ω + B ω)) :=
      (tendsto_const_nhds.add hm).add hb
    exact le_of_tendsto_of_tendsto hy hsum (Filter.Eventually.of_forall hbound)
  have hEInt : Integrable (fun ω => M ω + B ω) P :=
    hMInt.add hBInt
  have hEMean : (∫ ω, M ω + B ω ∂P) ≤ 0 := by
    rw [integral_add hMInt hBInt, hMMeanZero]
    simpa using hBMeanUpper
  refine ⟨fun ω => M ω + B ω, hEInt, hEMean, ?_⟩
  filter_upwards [hUpper] with ω hω
  simpa only [add_assoc] using hω
