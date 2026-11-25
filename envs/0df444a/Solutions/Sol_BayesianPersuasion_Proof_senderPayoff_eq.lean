-- Prove2me | solution 1 for BayesianPersuasion.Proof.senderPayoff_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:57:54.693167+00:00
-- url     : https://prove2.me/submissions/88466b1b-844f-4455-b5b0-abd9cd6c4d46

module
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BayesianPersuasion_Primitives

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
    (ha : SenderPreferred u v p a) : senderPayoff u v p = expected v p a := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨_, a, ha.1, rfl⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact ha.2 b hb
  · intro w hw
    exact ⟨_, ⟨a, ha.1, rfl⟩, hw⟩
end BayesianPersuasion.Proof
