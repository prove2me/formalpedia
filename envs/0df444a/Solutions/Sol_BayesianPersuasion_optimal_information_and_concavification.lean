-- Prove2me | solution 1 for BayesianPersuasion.optimal_information_and_concavification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:15:11.219724+00:00
-- url     : https://prove2.me/submissions/4dd38fd9-7572-4f2b-a481-298e1a1ab435

module
public import Definitions.Def_BayesianPersuasion_Attainment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Definitions.Def_BayesianPersuasion_Theorems
public import Theorems.Thm_BayesianPersuasion_Proof_concavification_concave
public import Theorems.Thm_BayesianPersuasion_Proof_concavification_le_majorant
public import Theorems.Thm_BayesianPersuasion_Proof_concavification_majorizes
public import Theorems.Thm_BayesianPersuasion_Proof_optimal_signal


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
theorem _root_.solution (p : Belief Ω) (hp : FullSupport p) :
    (∃ (k : ℕ) (_ : k ≤ Fintype.card Ω + 2) (π : Signal Ω k),
      signalValue u v p π = concavification u v p.val ∧
      ∀ (m : ℕ) (σ : Signal Ω m), signalValue u v p σ ≤ signalValue u v p π) ∧
    ConcaveOn ℝ (probabilitySimplex Ω) (concavification u v) ∧
    (∀ q : Belief Ω, senderPayoff u v q ≤ concavification u v q.val) ∧
    (∀ g : (Ω → ℝ) → ℝ, ConcaveOn ℝ (probabilitySimplex Ω) g →
      (∀ q : Belief Ω, senderPayoff u v q ≤ g q.val) →
      ∀ q : Belief Ω, concavification u v q.val ≤ g q.val) :=
  ⟨Proof.optimal_signal u v hu hv p hp, Proof.concavification_concave u v hu hv,
    Proof.concavification_majorizes u v hu hv, Proof.concavification_le_majorant u v hu hv⟩
end BayesianPersuasion
