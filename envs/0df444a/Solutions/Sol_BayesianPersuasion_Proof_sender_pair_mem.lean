-- Prove2me | solution 1 for BayesianPersuasion.Proof.sender_pair_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:18.924808+00:00
-- url     : https://prove2.me/submissions/64cb8b35-6c5c-42d0-bea7-52658da2a8d6

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_eq
public import Theorems.Thm_BayesianPersuasion_Proof_senderPreferred_exists


set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω]
open BayesianPersuasion.Proof
variable [TopologicalSpace A] [CompactSpace A] [Nonempty A] [T2Space A]
variable (u v : A → Ω → ℝ)
variable (hu : ∀ ω, Continuous (fun a => u a ω))
variable (hv : ∀ ω, Continuous (fun a => v a ω))
include hu hv
namespace BayesianPersuasion.Proof
theorem _root_.solution (p : Belief Ω) :
    (p.val, senderPayoff u v p) ∈ bestReplyPayoffs u v := by
  obtain ⟨a, ha⟩ := senderPreferred_exists u v hu hv p
  exact ⟨(p, a), ha.1, Prod.ext rfl (senderPayoff_eq u v hu hv p ha).symm⟩
end BayesianPersuasion.Proof
