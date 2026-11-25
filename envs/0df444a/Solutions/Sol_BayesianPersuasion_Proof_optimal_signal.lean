-- Prove2me | solution 1 for BayesianPersuasion.Proof.optimal_signal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:14:00.81439+00:00
-- url     : https://prove2.me/submissions/30a0e1ad-e734-4ca6-b6b0-c8bf48d8ff1a

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_split_le_concavification
public import Theorems.Thm_BayesianPersuasion_Proof_optimal_split
public import Theorems.Thm_BayesianPersuasion_Proof_signal_bayesPlausible
public import Theorems.Thm_BayesianPersuasion_Proof_splitting_payoff


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
theorem _root_.solution (p : Belief Ω) (hp : FullSupport p) :
    ∃ (k : ℕ) (_ : k ≤ Fintype.card Ω + 2) (π : Signal Ω k),
      signalValue u v p π = concavification u v p.val ∧
      ∀ (m : ℕ) (σ : Signal Ω m), signalValue u v p σ ≤ signalValue u v p π := by
  obtain ⟨k, hk, w, b, hb, hval⟩ := optimal_split u v hu hv p
  refine ⟨k, hk, splittingSignal p hp w b hb, ?_, ?_⟩
  · exact (splitting_payoff p hp w b hb (senderPayoff u v)).trans hval
  · intro m σ
    rw [show signalValue u v p (splittingSignal p hp w b hb) = concavification u v p.val from
      (splitting_payoff p hp w b hb (senderPayoff u v)).trans hval]
    exact split_le_concavification u v hu hv p (signalWeights p σ) (signalPosterior p σ)
      (signal_bayesPlausible p σ)
end BayesianPersuasion.Proof
