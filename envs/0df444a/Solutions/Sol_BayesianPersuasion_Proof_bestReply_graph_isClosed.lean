-- Prove2me | solution 1 for BayesianPersuasion.Proof.bestReply_graph_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:03:57.537796+00:00
-- url     : https://prove2.me/submissions/4bcff645-305c-42f5-af8a-fc2487270d85

module
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BayesianPersuasion_Primitives
public import Theorems.Thm_BayesianPersuasion_Proof_continuous_expected

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
namespace BayesianPersuasion.Proof
theorem _root_.solution (u : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω)) :
    IsClosed {x : Belief Ω × A | BestReply u x.1 x.2} := by
  unfold BestReply
  simp only [ofPred_forall]
  refine isClosed_iInter fun b => isClosed_le ?_ (continuous_expected u hu)
  exact (continuous_expected u hu).comp (continuous_fst.prodMk continuous_const)
end BayesianPersuasion.Proof
