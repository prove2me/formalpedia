-- Prove2me | solution 1 for BayesianPersuasion.persuasion_gain_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:16:28.500528+00:00
-- url     : https://prove2.me/submissions/aee6f4ca-f7f6-4256-9068-76096754fd43

module
public import Definitions.Def_BayesianPersuasion_Attainment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Definitions.Def_BayesianPersuasion_Theorems
public import Theorems.Thm_BayesianPersuasion_Proof_persuasion_gain_iff


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
    (∃ (n : ℕ) (π : Signal Ω n), senderPayoff u v p < signalValue u v p π) ↔
      senderPayoff u v p < concavification u v p.val :=
  Proof.persuasion_gain_iff u v hu hv p hp
end BayesianPersuasion
