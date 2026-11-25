-- Prove2me | solution 1 for BayesianPersuasion.economic_payoff_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:10:26.670257+00:00
-- url     : https://prove2.me/submissions/9708140b-9c0a-4881-aa8f-a891f1d6911e

module
public import Definitions.Def_BayesianPersuasion_Attainment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Definitions.Def_BayesianPersuasion_Theorems
public import Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_bounded
public import Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_eq
public import Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_upperSemicontinuous
public import Theorems.Thm_BayesianPersuasion_Proof_senderPreferred_exists


set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω] [Nonempty Ω]
variable [MetricSpace A] [CompactSpace A] [Nonempty A]
variable (u v : A → Ω → ℝ)
variable (hu : ∀ ω, Continuous (fun a => u a ω))
variable (hv : ∀ ω, Continuous (fun a => v a ω))
include hu hv
namespace BayesianPersuasion
theorem _root_.solution :
    (∀ p : Belief Ω, ∃ a, SenderPreferred u v p a ∧ senderPayoff u v p = expected v p a) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ p : Belief Ω, |senderPayoff u v p| ≤ M) ∧
    UpperSemicontinuous (senderPayoff u v) := by
  refine ⟨?_, Proof.senderPayoff_bounded u v hu hv,
    Proof.senderPayoff_upperSemicontinuous u v hu hv⟩
  intro p
  obtain ⟨a, ha⟩ := Proof.senderPreferred_exists u v hu hv p
  exact ⟨a, ha, Proof.senderPayoff_eq u v hu hv p ha⟩
end BayesianPersuasion
