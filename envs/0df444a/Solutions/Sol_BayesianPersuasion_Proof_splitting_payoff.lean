-- Prove2me | solution 1 for BayesianPersuasion.Proof.splitting_payoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:25.489977+00:00
-- url     : https://prove2.me/submissions/8901fefe-bfe9-4d76-8ab5-a51f866781a0

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_Signals
public import Theorems.Thm_BayesianPersuasion_Proof_splitting_mass
public import Theorems.Thm_BayesianPersuasion_Proof_splitting_posterior

set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} [Fintype Ω]
open BayesianPersuasion.Proof
namespace BayesianPersuasion.Proof
theorem _root_.solution (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b)
    (f : Belief Ω → ℝ) :
    ∑ s, signalMass p (splittingSignal p hp w b hb) s *
      f (signalPosterior p (splittingSignal p hp w b hb) s) = ∑ s, w.val s * f (b s) := by
  apply Finset.sum_congr rfl
  intro s _
  rw [splitting_mass]
  by_cases hs : w.val s = 0
  · simp [hs]
  · rw [splitting_posterior p hp w b hb s hs]
end BayesianPersuasion.Proof
