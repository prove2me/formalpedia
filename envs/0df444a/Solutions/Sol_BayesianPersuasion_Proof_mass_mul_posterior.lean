-- Prove2me | solution 1 for BayesianPersuasion.Proof.mass_mul_posterior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:57.367+00:00
-- url     : https://prove2.me/submissions/e321cfbf-964d-48bc-bb3d-0dfad2a30cda

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_Signals
public import Theorems.Thm_BayesianPersuasion_Proof_joint_eq_zero_of_null

set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} [Fintype Ω]
open BayesianPersuasion.Proof
namespace BayesianPersuasion.Proof
theorem _root_.solution (p : Belief Ω) {n : ℕ} (π : Signal Ω n)
    (s : Fin n) (ω : Ω) :
    signalMass p π s * (signalPosterior p π s).val ω = p.val ω * (π ω).val s := by
  classical
  change signalMass p π s * posteriorVector p π s ω = _
  unfold posteriorVector
  split_ifs with h
  · simp only [h, zero_mul]
    exact (joint_eq_zero_of_null p π s h ω).symm
  · field_simp
end BayesianPersuasion.Proof
