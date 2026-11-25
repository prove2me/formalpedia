-- Prove2me | solution 1 for BayesianPersuasion.Proof.signal_bayesPlausible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:35.066832+00:00
-- url     : https://prove2.me/submissions/c313fafd-6ee9-41df-9681-6f001148ee51

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_Signals
public import Theorems.Thm_BayesianPersuasion_Proof_mass_mul_posterior

set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} [Fintype Ω]
open BayesianPersuasion.Proof
namespace BayesianPersuasion.Proof
theorem _root_.solution (p : Belief Ω) {n : ℕ} (π : Signal Ω n) :
    BayesPlausible p (signalWeights p π) (signalPosterior p π) := by
  intro ω
  change ∑ s, signalMass p π s * (signalPosterior p π s).val ω = _
  simp_rw [mass_mul_posterior, ← Finset.mul_sum, (π ω).property.2, mul_one]
end BayesianPersuasion.Proof
