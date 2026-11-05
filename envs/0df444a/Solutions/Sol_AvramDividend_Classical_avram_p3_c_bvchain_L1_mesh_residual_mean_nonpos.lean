-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_L1_mesh_residual_mean_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:41:24.239689+00:00
-- url     : https://prove2.me/submissions/e31ad933-08c3-4ae0-bbd7-b776f0060ccb

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter

/-- Nonpositive finite-grid means pass through a vanishing L1 mesh error. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : Ω → ℝ) (Rmesh : ℕ → Ω → ℝ)
    (hR : Integrable R P)
    (hMesh : ∀ n, Integrable (Rmesh n) P)
    (hMean : ∀ n, (∫ ω, Rmesh n ω ∂P) ≤ 0)
    (hError : Tendsto (fun n => (∫ ω, |Rmesh n ω - R ω| ∂P))
      atTop (nhds (0 : ℝ))) :
    (∫ ω, R ω ∂P) ≤ 0 := by
  have hBound (n : ℕ) :
      (∫ ω, R ω ∂P) ≤ (∫ ω, |Rmesh n ω - R ω| ∂P) := by
    have hSub : Integrable (fun ω => Rmesh n ω - R ω) P :=
      (hMesh n).sub hR
    have hAbs : Integrable (fun ω => |Rmesh n ω - R ω|) P :=
      hSub.abs
    have hPoint : ∀ᵐ ω ∂P,
        R ω ≤ Rmesh n ω + |Rmesh n ω - R ω| :=
      Filter.Eventually.of_forall (fun ω => by
        have h := neg_le_abs (Rmesh n ω - R ω)
        linarith)
    have hMon := integral_mono_ae hR ((hMesh n).add hAbs) hPoint
    have hAddEq :
        (∫ ω, Rmesh n ω + |Rmesh n ω - R ω| ∂P) =
          (∫ ω, Rmesh n ω ∂P) +
            (∫ ω, |Rmesh n ω - R ω| ∂P) := by
      simpa only [Pi.add_apply] using (integral_add (hMesh n) hAbs)
    have hMon' :
        (∫ ω, R ω ∂P) ≤
          (∫ ω, Rmesh n ω + |Rmesh n ω - R ω| ∂P) := by
      simpa only [Pi.add_apply] using hMon
    rw [hAddEq] at hMon'
    linarith [hMean n]
  exact ge_of_tendsto hError (Filter.Eventually.of_forall hBound)
