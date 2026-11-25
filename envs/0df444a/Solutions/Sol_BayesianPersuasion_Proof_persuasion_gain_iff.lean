-- Prove2me | solution 1 for BayesianPersuasion.Proof.persuasion_gain_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:14:59.300011+00:00
-- url     : https://prove2.me/submissions/4c4073f5-17d7-45e5-a980-866bc93a0a75

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_split_le_concavification
public import Theorems.Thm_BayesianPersuasion_Proof_optimal_signal
public import Theorems.Thm_BayesianPersuasion_Proof_signal_bayesPlausible


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
    (∃ (n : ℕ) (π : Signal Ω n), senderPayoff u v p < signalValue u v p π) ↔
      senderPayoff u v p < concavification u v p.val := by
  constructor
  · rintro ⟨n, π, hπ⟩
    exact hπ.trans_le (split_le_concavification u v hu hv p
      (signalWeights p π) (signalPosterior p π) (signal_bayesPlausible p π))
  · intro h
    obtain ⟨n, _, π, hπ, _⟩ := optimal_signal u v hu hv p hp
    exact ⟨n, π, by simpa only [hπ] using h⟩
end BayesianPersuasion.Proof
