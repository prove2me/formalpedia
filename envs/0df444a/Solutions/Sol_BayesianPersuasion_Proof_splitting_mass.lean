-- Prove2me | solution 1 for BayesianPersuasion.Proof.splitting_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:04:11.496593+00:00
-- url     : https://prove2.me/submissions/ef53c0f2-2c4f-42c9-b44a-b6fb0cacfeb1

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_Signals
public import Theorems.Thm_BayesianPersuasion_Proof_splitting_joint

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
    (s : Fin n) : signalMass p (splittingSignal p hp w b hb) s = w.val s := by
  unfold signalMass
  simp_rw [splitting_joint, ← Finset.mul_sum, (b s).property.2, mul_one]
end BayesianPersuasion.Proof
