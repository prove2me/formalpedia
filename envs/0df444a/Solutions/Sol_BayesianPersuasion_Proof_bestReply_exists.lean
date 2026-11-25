-- Prove2me | solution 1 for BayesianPersuasion.Proof.bestReply_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:15.641794+00:00
-- url     : https://prove2.me/submissions/3103f6f1-9dd5-48dc-b46e-14bb5f4fc9e4

module
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BayesianPersuasion_Primitives
public import Theorems.Thm_BayesianPersuasion_Proof_continuous_expected_action

set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable (Ω : Type uΩ) [Fintype Ω]
variable {Ω} {A : Type uA}
open BayesianPersuasion.Proof
variable [TopologicalSpace A]
variable [CompactSpace A] [Nonempty A]
namespace BayesianPersuasion.Proof
theorem _root_.solution (u : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω)) (p : Belief Ω) :
    ∃ a, BestReply u p a := by
  obtain ⟨a, _, ha⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_expected_action u hu p).continuousOn
  exact ⟨a, fun b => ha (Set.mem_univ b)⟩
end BayesianPersuasion.Proof
