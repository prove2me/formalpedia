-- Prove2me | solution 1 for BayesianPersuasion.Proof.senderPreferred_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:51.232799+00:00
-- url     : https://prove2.me/submissions/7e3bed2c-e428-410a-8dcf-bf1927782db2

module
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BayesianPersuasion_Primitives
public import Theorems.Thm_BayesianPersuasion_Proof_continuous_expected_action
public import Theorems.Thm_BayesianPersuasion_Proof_bestReply_isClosed
public import Theorems.Thm_BayesianPersuasion_Proof_bestReply_exists

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
theorem _root_.solution (u v : A → Ω → ℝ)
    (hu : ∀ ω, Continuous (fun a => u a ω))
    (hv : ∀ ω, Continuous (fun a => v a ω)) (p : Belief Ω) :
    ∃ a, SenderPreferred u v p a := by
  obtain ⟨a, ha⟩ := bestReply_exists u hu p
  obtain ⟨b, hb, hmax⟩ := (bestReply_isClosed u hu p).isCompact.exists_isMaxOn
    ⟨a, ha⟩ (continuous_expected_action v hv p).continuousOn
  exact ⟨b, hb, hmax⟩
end BayesianPersuasion.Proof
