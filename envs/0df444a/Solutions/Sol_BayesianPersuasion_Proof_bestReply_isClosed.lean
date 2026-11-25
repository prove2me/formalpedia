-- Prove2me | solution 1 for BayesianPersuasion.Proof.bestReply_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:14.956115+00:00
-- url     : https://prove2.me/submissions/10dbb897-f4dd-4cb4-bb1b-451b92827196

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
namespace BayesianPersuasion.Proof
theorem _root_.solution (u : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω)) (p : Belief Ω) :
    IsClosed {a | BestReply u p a} := by
  unfold BestReply
  simp only [ofPred_forall]
  exact isClosed_iInter fun b => isClosed_le continuous_const (continuous_expected_action u hu p)
end BayesianPersuasion.Proof
