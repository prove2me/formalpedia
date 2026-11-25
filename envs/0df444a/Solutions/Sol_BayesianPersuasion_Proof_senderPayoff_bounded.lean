-- Prove2me | solution 1 for BayesianPersuasion.Proof.senderPayoff_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:20.236436+00:00
-- url     : https://prove2.me/submissions/5f699048-4e3d-4074-81f0-38c0bb9468a0

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_continuous_expected
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
theorem _root_.solution :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : Belief Ω, |senderPayoff u v p| ≤ M := by
  have hcont : Continuous (fun x : Belief Ω × A => |expected v x.1 x.2|) :=
    (continuous_expected v hv).abs
  obtain ⟨M, hM⟩ := (isCompact_range hcont).bddAbove
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro p
  obtain ⟨a, ha⟩ := senderPreferred_exists u v hu hv p
  rw [senderPayoff_eq u v hu hv p ha]
  exact (hM ⟨(p, a), rfl⟩).trans (le_max_left _ _)
end BayesianPersuasion.Proof
