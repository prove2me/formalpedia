-- Prove2me | solution 1 for BookProof.NavierStokesFlow.IkebeKato.exists_finiteModes_graph_approx
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T12:32:07.381926+00:00
-- url     : https://prove2.me/submissions/f3d80096-813d-4257-8d4f-6853350ec704

-- Generated from ChapterNavierStokesIkebeKato.lean — solution of BookProof.NavierStokesFlow.IkebeKato.exists_finiteModes_graph_approx
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_coe_sum_single
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_sum_single_mem_finiteModes
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato



open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (c : ι → ℝ) (x : maxDom c) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : maxDom c, (y : L2I ι) ∈ lpFiniteModes ι ∧
      ‖(y : L2I ι) - (x : L2I ι)‖ < ε ∧ ‖diagMax c y - diagMax c x‖ < ε := by

  classical
  set u : ι → ℂ := fun k => ((x : L2I ι) : ι → ℂ) k with hu
  set v : ι → ℂ := fun k => ((diagMax c x : L2I ι) : ι → ℂ) k with hv
  have hxsum : HasSum (fun i => lp.single 2 i (u i)) ((x : L2I ι)) :=
    lp.hasSum_single (by norm_num) _
  have hvsum : HasSum (fun i => lp.single 2 i (v i)) ((diagMax c x : L2I ι)) :=
    lp.hasSum_single (by norm_num) _
  have hx1 : ∀ᶠ S : Finset ι in Filter.atTop,
      ‖(∑ i ∈ S, lp.single 2 i (u i) : L2I ι) - (x : L2I ι)‖ < ε := by
    have hmet := Metric.tendsto_atTop.mp hxsum
    obtain ⟨S₀, hS₀⟩ := hmet ε hε
    filter_upwards [Filter.eventually_ge_atTop S₀] with S hS
    have := hS₀ S hS
    rwa [dist_eq_norm] at this
  have hx2 : ∀ᶠ S : Finset ι in Filter.atTop,
      ‖(∑ i ∈ S, lp.single 2 i (v i) : L2I ι) - (diagMax c x : L2I ι)‖ < ε := by
    have hmet := Metric.tendsto_atTop.mp hvsum
    obtain ⟨S₀, hS₀⟩ := hmet ε hε
    filter_upwards [Filter.eventually_ge_atTop S₀] with S hS
    have := hS₀ S hS
    rwa [dist_eq_norm] at this
  obtain ⟨S, hS1, hS2⟩ := (hx1.and hx2).exists
  refine ⟨⟨(∑ i ∈ S, lp.single 2 i (u i) : L2I ι),
    finiteModes_le_maxDom c (sum_single_mem_finiteModes S u)⟩,
    sum_single_mem_finiteModes S u, hS1, ?_⟩
  have hdiag : (diagMax c ⟨(∑ i ∈ S, lp.single 2 i (u i) : L2I ι),
      finiteModes_le_maxDom c (sum_single_mem_finiteModes S u)⟩ : L2I ι)
      = (∑ i ∈ S, lp.single 2 i (v i) : L2I ι) := by
    refine lp.ext (funext fun k => ?_)
    rw [diagMax_coe, coe_sum_single, coe_sum_single]
    by_cases hk : k ∈ S
    · simp [hk, hv, hu]
    · simp [hk]
  rw [hdiag]
  exact hS2
