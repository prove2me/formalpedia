-- Prove2me | solution 1 for AvramDividend.Classical.eqOn_Ioi_of_ae_eq_of_continuous_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T23:10:14.914051+00:00
-- url     : https://prove2.me/submissions/6c456d0c-4808-427d-b6e9-9540a13e6e0b

import Mathlib

open MeasureTheory Filter Set Topology
open scoped ENNReal

theorem solution
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Ioi (0 : ℝ)))
    (hg : ∀ x : ℝ, 0 < x →
      ContinuousWithinAt g (Ici x) x)
    (hfg : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) :
    ∀ x : ℝ, 0 < x → f x = g x := by
  have hae :
      ∀ᵐ y : ℝ ∂volume, y ∈ Ioi (0 : ℝ) → f y = g y :=
    ae_imp_of_ae_restrict hfg
  let E : Set ℝ :=
    {y : ℝ | y ∈ Ioi (0 : ℝ) → f y = g y}
  have hE : Dense E := by
    simpa [E] using (volume.dense_of_ae hae)
  intro x hx
  have hs_eq : EqOn f g (Ioi x ∩ E) := by
    intro y hy
    exact hy.2 (lt_trans hx (mem_Ioi.mp hy.1))
  have hs_f : Ioi x ∩ E ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact mem_Ioi.mpr (lt_trans hx (mem_Ioi.mp hy.1))
  have hs_g : Ioi x ∩ E ⊆ Ici x := by
    intro y hy
    exact mem_Ici.mpr (le_of_lt (mem_Ioi.mp hy.1))
  have hioi : Ioi x ⊆ closure (Ioi x ∩ E) :=
    hE.open_subset_closure_inter isOpen_Ioi
  have hici : Ici x ⊆ closure (Ioi x ∩ E) := by
    rw [← closure_Ioi x]
    exact closure_minimal hioi isClosed_closure
  have hxcl : x ∈ closure (Ioi x ∩ E) :=
    hici (mem_Ici.mpr le_rfl)
  haveI : (𝓝[Ioi x ∩ E] x).NeBot :=
    mem_closure_iff_clusterPt.mp hxcl
  exact
    tendsto_nhds_unique_of_eventuallyEq
      ((hf x hx).mono_left <| nhdsWithin_mono _ hs_f)
      ((hg x hx).mono_left <| nhdsWithin_mono _ hs_g)
      (hs_eq.eventuallyEq_of_mem self_mem_nhdsWithin)
