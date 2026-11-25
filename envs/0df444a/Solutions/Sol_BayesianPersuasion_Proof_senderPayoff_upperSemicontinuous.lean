-- Prove2me | solution 1 for BayesianPersuasion.Proof.senderPayoff_upperSemicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:45.632263+00:00
-- url     : https://prove2.me/submissions/8573f7ad-2633-407a-a85c-b024e8b8e1f0

module
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BayesianPersuasion_Primitives
public import Theorems.Thm_BayesianPersuasion_Proof_continuous_expected
public import Theorems.Thm_BayesianPersuasion_Proof_bestReply_graph_isClosed
public import Theorems.Thm_BayesianPersuasion_Proof_senderPreferred_exists
public import Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_eq
public import Theorems.Thm_BayesianPersuasion_Proof_bestReply_le_senderPayoff

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
    (hv : ∀ ω, Continuous (fun a => v a ω)) :
    UpperSemicontinuous (senderPayoff u v) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro c
  have hc : IsClosed {x : Belief Ω × A | BestReply u x.1 x.2 ∧ c ≤ expected v x.1 x.2} :=
    (bestReply_graph_isClosed u hu).inter (isClosed_le continuous_const (continuous_expected v hv))
  have heq : senderPayoff u v ⁻¹' Ici c =
      Prod.fst '' {x : Belief Ω × A | BestReply u x.1 x.2 ∧ c ≤ expected v x.1 x.2} := by
    ext p
    constructor
    · intro hp
      obtain ⟨a, ha⟩ := senderPreferred_exists u v hu hv p
      exact ⟨(p, a), ⟨ha.1, by simpa [senderPayoff_eq u v hu hv p ha] using hp⟩, rfl⟩
    · rintro ⟨⟨q, a⟩, ⟨ha, hc⟩, rfl⟩
      exact hc.trans (bestReply_le_senderPayoff u v hu hv q ha)
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ hc
end BayesianPersuasion.Proof
