-- Prove2me | solution 1 for BianchiIX.contDiffAt_normalizedMaxCurve_nat
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:12:27.316342+00:00
-- url     : https://prove2.me/submissions/5476b6d2-1b4c-4f66-aa76-a95c4179962f

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Theorems.Thm_BianchiIX_contDiff_normalizedField
import Theorems.Thm_BianchiIX_exists_ode_local_contDiff_succ
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
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
open scoped Topology ContDiff

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.isOpen_normalizedFlowDomain (t₀ : ℝ) : IsOpen (normalizedFlowDomain t₀) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact mem_interior_iff_mem_nhds.mp (normalizedMaxCurve_regular hz).1

end
end

private theorem BianchiIX.exists_normalizedMaxCurve_local_contDiff_nat (n : ℕ) (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      (∀ x ∈ ball x₀ r, Ioo (t₀ - ε) (t₀ + ε) ⊆ normalizedMaxDomain x t₀) ∧
      ContDiffOn ℝ n (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
        (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨r, hr, ε, hε, α, hcα, hα⟩ :=
    exists_ode_local_contDiff_succ n (contDiff_normalizedField ∞) x₀ t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  let S (x : NormalizedState) (hx : x ∈ ball x₀ r) : NormalizedSolution x t₀ :=
    ⟨Ioo (t₀ - ε) (t₀ + ε), isOpen_Ioo, convex_Ioo _ _, ht₀,
      fun t => α (x, t), (hα x hx).1, (hα x hx).2⟩
  refine ⟨r, hr, ε, hε, fun x hx => (S x hx).domain_subset_maximal, ?_⟩
  exact (hcα.of_le (le_add_of_nonneg_right zero_le_one)).congr
    (fun z hz => normalizedMaxCurve_eqOn (S z.1 hz.1) hz.2)

/-- Finite-order regularity propagates by restarting the exact maximal flow. -/
theorem solution (n : ℕ) {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ n (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) := by
  let S : Set (NormalizedState × ℝ) := {z | z ∈ normalizedFlowDomain t₀ ∧
    ContDiffAt ℝ n (fun w : NormalizedState × ℝ => normalizedMaxCurve w.1 t₀ w.2) z}
  have hoS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    filter_upwards [(isOpen_normalizedFlowDomain t₀).mem_nhds hz.1,
      hz.2.eventually (by simp)] with w hw hd
    exact ⟨hw, hd⟩
  have hinit : (x, t₀) ∈ S := by
    obtain ⟨r, hr, ε, hε, _, hc⟩ := exists_normalizedMaxCurve_local_contDiff_nat n x t₀
    exact ⟨initial_mem_normalizedMaxDomain x t₀,
      hc.contDiffAt (prod_mem_nhds (ball_mem_nhds _ hr) (Ioo_mem_nhds (by linarith) (by linarith)))⟩
  have hrestart {s b : ℝ} {y : NormalizedState} {r ε : ℝ} (hs : (x, s) ∈ S)
      (hdom : ∀ z ∈ ball y r, Ioo (-ε) ε ⊆ normalizedMaxDomain z 0)
      (hc : ContDiffOn ℝ n (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 0 z.2)
        (ball y r ×ˢ Ioo (-ε) ε))
      (hy : normalizedMaxCurve x t₀ s ∈ ball y r) (hb : b - s ∈ Ioo (-ε) ε) : (x, b) ∈ S := by
    let g : NormalizedState × ℝ → NormalizedState × ℝ := fun z =>
      (normalizedMaxCurve z.1 t₀ s, z.2 - s)
    have hg : ContDiffAt ℝ n g (x, b) :=
      (hs.2.comp (x, b) (contDiffAt_fst.prodMk contDiffAt_const)).prodMk
        (contDiffAt_snd.sub contDiffAt_const)
    have hV : ball y r ×ˢ Ioo (-ε) ε ∈ 𝓝 (g (x, b)) :=
      (isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hy, hb⟩
    have hcomp := (hc.contDiffAt hV).comp (x, b) hg
    have hstart : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, b), s ∈ normalizedMaxDomain z.1 t₀ := by
      have hemb : ContinuousAt (fun z : NormalizedState × ℝ => (z.1, s)) (x, b) := by fun_prop
      exact hemb.eventually ((isOpen_normalizedFlowDomain t₀).mem_nhds hs.1)
    have H : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, b), z ∈ normalizedFlowDomain t₀ ∧
        normalizedMaxCurve z.1 t₀ z.2 = normalizedMaxCurve (g z).1 0 (g z).2 := by
      filter_upwards [hstart, hg.continuousAt.eventually hV] with z hz hv
      exact normalizedMaxCurve_restart hz (hdom _ hv.1 hv.2)
    exact ⟨H.self_of_nhds.1, hcomp.congr_of_eventuallyEq (H.mono fun _ h => h.2)⟩
  let R : Set ℝ := (fun u => (x, u)) ⁻¹' S
  have hoR : IsOpen R := hoS.preimage (by fun_prop)
  have hnonempty : (normalizedMaxDomain x t₀ ∩ R).Nonempty :=
    ⟨t₀, initial_mem_normalizedMaxDomain x t₀, hinit⟩
  have hclosed : closure R ∩ normalizedMaxDomain x t₀ ⊆ R := by
    intro b hb
    obtain ⟨r, hr, ε, hε, hdom, hc⟩ :=
      exists_normalizedMaxCurve_local_contDiff_nat n (normalizedMaxCurve x t₀ b) 0
    simp only [zero_sub, zero_add] at hdom hc
    have hstate : ∀ᶠ s in 𝓝 b, normalizedMaxCurve x t₀ s ∈ ball (normalizedMaxCurve x t₀ b) r :=
      (hasDerivAt_normalizedMaxCurve hb.2).continuousAt.eventually (ball_mem_nhds _ hr)
    have htime : ∀ᶠ s : ℝ in 𝓝 b, b - s ∈ Ioo (-ε) ε := by
      have H : ContinuousAt (fun s : ℝ => b - s) b := by fun_prop
      exact H.eventually (Ioo_mem_nhds (by dsimp; linarith) (by dsimp; linarith))
    obtain ⟨s, hs, hss, hst⟩ :=
      ((mem_closure_iff_frequently.mp hb.1).and_eventually (hstate.and htime)).exists
    exact hrestart hs hdom hc hss hst
  exact ((convex_normalizedMaxDomain x t₀).isPreconnected.subset_of_closure_inter_subset
    hoR hnonempty hclosed ht).2
