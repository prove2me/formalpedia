-- Prove2me | solution 1 for BayesianPersuasion.Proof.bestReply_le_senderPayoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:19.650801+00:00
-- url     : https://prove2.me/submissions/6bb80189-cb7e-49aa-a0fe-8036c4fba381

module
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BayesianPersuasion_Primitives
public import Theorems.Thm_BayesianPersuasion_Proof_senderPreferred_exists
public import Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_eq

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
    (hv : ∀ ω, Continuous (fun a => v a ω)) (p : Belief Ω) {a : A}
    (ha : BestReply u p a) : expected v p a ≤ senderPayoff u v p := by
  obtain ⟨b, hb⟩ := senderPreferred_exists u v hu hv p
  rw [senderPayoff_eq u v hu hv p hb]
  exact hb.2 a ha
end BayesianPersuasion.Proof
