-- Prove2me | solution 1 for ConnesGreen.canonical_actor_test_norms_window_independent
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T00:31:46.240089+00:00
-- url     : https://prove2.me/submissions/516f15bc-4cf4-4ef8-88d7-8b142ff79854

import Theorems.Thm_ConnesGreen_exists_original_window_actor_inclusion
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
private theorem nested_original_test_energies
    (t T : ℝ) (ht : 0 < t) (hT : 0 < T) (htT : t ≤ T)
    (S : Finset CriticalZeros) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 =
      ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ∧
    ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 =
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 := by
  obtain ⟨U, hU, _, hP, hN⟩ := exists_original_window_actor_inclusion t T ht hT htT S
  have hp := congrArg (fun A => A.adjoint (sourceEmbed t (problemOneL g))) hP
  have hn := congrArg (fun A => A.adjoint (sourceEmbed t (problemOneL g))) hN
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply] at hp hn
  change (canonicalPositiveSynthesis T hT).adjoint (U (sourceEmbed t (problemOneL g))) = _ at hp
  change (canonicalSelectedSynthesis T hT S).adjoint (U (sourceEmbed t (problemOneL g))) = _ at hn
  rw [hU g hg] at hp hn
  exact ⟨congrArg (fun x => ‖x‖ ^ 2) hp, congrArg (fun x => ‖x‖ ^ 2) hn⟩

theorem solution (t T : ℝ) (ht : 0 < t)
    (hT : 0 < T) (S : Finset CriticalZeros) (g : ℝ → ℂ)
    (hg : SupportedTest t g) (hgT : SupportedTest T g) :
    ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 =
      ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ∧
    ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 =
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 := by
  rcases le_total t T with h | h
  · exact nested_original_test_energies t T ht hT h S g hg
  · obtain ⟨hp, hn⟩ := nested_original_test_energies T t hT ht h S g hgT
    exact ⟨hp.symm, hn.symm⟩
