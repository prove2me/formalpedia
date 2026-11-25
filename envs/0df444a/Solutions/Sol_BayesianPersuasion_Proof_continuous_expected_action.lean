-- Prove2me | solution 1 for BayesianPersuasion.Proof.continuous_expected_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:01:06.216143+00:00
-- url     : https://prove2.me/submissions/06ebffea-11a7-4e0a-b0e1-f93d07191388

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
    (hu : ∀ ω, Continuous (fun a => u a ω)) (p : Belief Ω) :
    Continuous (expected u p) :=
  (continuous_expected u hu).comp (continuous_const.prodMk continuous_id)
end BayesianPersuasion.Proof
