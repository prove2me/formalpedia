-- Prove2me | solution 1 for BayesianPersuasion.Proof.senderPayoff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:10:27.702947+00:00
-- url     : https://prove2.me/submissions/adbf395f-f967-4510-b467-1be2a9d63c76

module
public import Definitions.Def_BayesianPersuasion_Attainment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Definitions.Def_BayesianPersuasion_Theorems
public import Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_upperSemicontinuous


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
open BayesianPersuasion.Proof
include hu hv
namespace BayesianPersuasion.Proof
theorem _root_.solution [MeasurableSpace (Belief Ω)] [BorelSpace (Belief Ω)] :
    Measurable (senderPayoff u v) :=
  (senderPayoff_upperSemicontinuous u v hu hv).measurable
end BayesianPersuasion.Proof
