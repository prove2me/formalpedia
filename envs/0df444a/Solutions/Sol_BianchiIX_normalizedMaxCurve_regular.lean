-- Prove2me | solution 1 for BianchiIX.normalizedMaxCurve_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:24:36.165505+00:00
-- url     : https://prove2.me/submissions/c415735a-5612-4ee2-98dc-3a5dc99a9ef7

import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Theorems.Thm_BianchiIX_exists_normalizedMaxCurve_local_contDiff
import Theorems.Thm_BianchiIX_normalizedMaxCurve_restart
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private def BianchiIX.regularFlowDomain (t₀ : ℝ) : Set (NormalizedState × ℝ) :=
  {z | z ∈ interior (normalizedFlowDomain t₀) ∧
    ContDiffAt ℝ 1 (fun w : NormalizedState × ℝ => normalizedMaxCurve w.1 t₀ w.2) z}

private theorem BianchiIX.isOpen_regularFlowDomain (t₀ : ℝ) : IsOpen (regularFlowDomain t₀) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  filter_upwards [isOpen_interior.mem_nhds hz.1, hz.2.eventually (by norm_num)] with w hw hd
  exact ⟨hw, hd⟩

private theorem BianchiIX.initial_mem_regularFlowDomain (x : NormalizedState) (t₀ : ℝ) :
    (x, t₀) ∈ regularFlowDomain t₀ := by
  obtain ⟨r, hr, ε, hε, hdom, hc⟩ := exists_normalizedMaxCurve_local_contDiff x t₀
  have hnhds : ball x r ×ˢ Ioo (t₀ - ε) (t₀ + ε) ∈ 𝓝 (x, t₀) :=
    prod_mem_nhds (ball_mem_nhds _ hr) (Ioo_mem_nhds (by linarith) (by linarith))
  exact ⟨mem_interior_iff_mem_nhds.mpr (mem_of_superset hnhds fun z hz => hdom z.1 hz.1 hz.2),
    hc.contDiffAt hnhds⟩

private theorem BianchiIX.regularFlowDomain_restart {x y : NormalizedState} {t₀ s t r ε : ℝ}
    (hs : (x, s) ∈ regularFlowDomain t₀)
    (hdom : ∀ z ∈ ball y r, Ioo (-ε) ε ⊆ normalizedMaxDomain z 0)
    (hc : ContDiffOn ℝ 1 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 0 z.2)
      (ball y r ×ˢ Ioo (-ε) ε))
    (hy : normalizedMaxCurve x t₀ s ∈ ball y r) (ht : t - s ∈ Ioo (-ε) ε) :
    (x, t) ∈ regularFlowDomain t₀ := by
  let g : NormalizedState × ℝ → NormalizedState × ℝ := fun z =>
    (normalizedMaxCurve z.1 t₀ s, z.2 - s)
  have hg : ContDiffAt ℝ 1 g (x, t) :=
    (hs.2.comp (x, t) (contDiffAt_fst.prodMk contDiffAt_const)).prodMk
      (contDiffAt_snd.sub contDiffAt_const)
  have hV : ball y r ×ˢ Ioo (-ε) ε ∈ 𝓝 (g (x, t)) :=
    (isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hy, ht⟩
  have hcomp := (hc.contDiffAt hV).comp (x, t) hg
  have hstart : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t), s ∈ normalizedMaxDomain z.1 t₀ := by
    have hemb : ContinuousAt (fun z : NormalizedState × ℝ => (z.1, s)) (x, t) := by fun_prop
    exact hemb.eventually (show normalizedFlowDomain t₀ ∈ 𝓝 (x, s) from
      mem_interior_iff_mem_nhds.mp hs.1)
  have hlocal := hg.continuousAt.eventually hV
  have H : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t),
      z ∈ normalizedFlowDomain t₀ ∧
        normalizedMaxCurve z.1 t₀ z.2 = normalizedMaxCurve (g z).1 0 (g z).2 := by
    filter_upwards [hstart, hlocal] with z hz hv
    exact normalizedMaxCurve_restart hz (hdom _ hv.1 hv.2)
  exact ⟨mem_interior_iff_mem_nhds.mpr (H.mono fun _ h => h.1),
    hcomp.congr_of_eventuallyEq (H.mono fun _ h => h.2)⟩

/-- Local smoothness propagates through the entire maximal interval by connectedness. -/
theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    (x, t) ∈ interior (normalizedFlowDomain t₀) ∧
      ContDiffAt ℝ 1 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) := by
  let R : Set ℝ := (fun u => (x, u)) ⁻¹' regularFlowDomain t₀
  have hoR : IsOpen R := (isOpen_regularFlowDomain t₀).preimage (by fun_prop)
  have hinit : (normalizedMaxDomain x t₀ ∩ R).Nonempty :=
    ⟨t₀, initial_mem_normalizedMaxDomain x t₀, initial_mem_regularFlowDomain x t₀⟩
  apply (convex_normalizedMaxDomain x t₀).isPreconnected.subset_of_closure_inter_subset hoR hinit ?_ ht
  intro b hb
  obtain ⟨r, hr, ε, hε, hdom, hc⟩ :=
    exists_normalizedMaxCurve_local_contDiff (normalizedMaxCurve x t₀ b) 0
  simp only [zero_sub, zero_add] at hdom hc
  have hstate : ∀ᶠ s in 𝓝 b, normalizedMaxCurve x t₀ s ∈ ball (normalizedMaxCurve x t₀ b) r :=
    (hasDerivAt_normalizedMaxCurve hb.2).continuousAt.eventually (ball_mem_nhds _ hr)
  have htime : ∀ᶠ s : ℝ in 𝓝 b, b - s ∈ Ioo (-ε) ε := by
    have hcsub : ContinuousAt (fun s : ℝ => b - s) b := by fun_prop
    exact hcsub.eventually (Ioo_mem_nhds (by dsimp; linarith) (by dsimp; linarith))
  obtain ⟨s, hsR, hsstate, hstime⟩ :=
    ((mem_closure_iff_frequently.mp hb.1).and_eventually (hstate.and htime)).exists
  exact regularFlowDomain_restart hsR hdom hc hsstate hstime
