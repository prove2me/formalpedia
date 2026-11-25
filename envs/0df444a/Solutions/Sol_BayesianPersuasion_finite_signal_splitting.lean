-- Prove2me | solution 1 for BayesianPersuasion.finite_signal_splitting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:09:18.648904+00:00
-- url     : https://prove2.me/submissions/e7b8db65-9742-4570-90b9-33f1923993d7

module
public import Definitions.Def_BayesianPersuasion_Attainment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Definitions.Def_BayesianPersuasion_Theorems
public import Theorems.Thm_BayesianPersuasion_Proof_splitting_joint
public import Theorems.Thm_BayesianPersuasion_Proof_splitting_payoff
public import Theorems.Thm_BayesianPersuasion_Proof_splitting_posterior


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
namespace BayesianPersuasion
theorem _root_.solution (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) :
    BayesPlausible p w b ↔ ∃ π : Signal Ω n,
      (∀ s ω, p.val ω * (π ω).val s = w.val s * (b s).val ω) ∧
      (∀ s, w.val s ≠ 0 → signalPosterior p π s = b s) ∧
      signalValue u v p π = splitValue u v w b := by
  constructor
  · intro hb
    exact ⟨splittingSignal p hp w b hb,
      fun s ω => Proof.splitting_joint p hp w b hb ω s,
      Proof.splitting_posterior p hp w b hb,
      Proof.splitting_payoff p hp w b hb (senderPayoff u v)⟩
  · rintro ⟨π, hj, _, _⟩ ω
    calc
      ∑ s, w.val s * (b s).val ω = ∑ s, p.val ω * (π ω).val s :=
        Finset.sum_congr rfl fun s _ => (hj s ω).symm
      _ = p.val ω := by rw [← Finset.mul_sum, (π ω).property.2, mul_one]
end BayesianPersuasion
