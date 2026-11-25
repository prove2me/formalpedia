-- Prove2me | solution 1 for BayesianPersuasion.Proof.splitting_posterior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:26.950577+00:00
-- url     : https://prove2.me/submissions/7691cc6b-6165-44d7-80b5-3dc9dfba91ce

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_Signals
public import Theorems.Thm_BayesianPersuasion_Proof_splitting_joint
public import Theorems.Thm_BayesianPersuasion_Proof_splitting_mass

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
    (s : Fin n) (hs : w.val s ≠ 0) :
    signalPosterior p (splittingSignal p hp w b hb) s = b s := by
  apply Subtype.ext
  funext ω
  change posteriorVector _ _ _ _ = _
  unfold posteriorVector
  rw [splitting_mass, if_neg hs, splitting_joint]
  field_simp
end BayesianPersuasion.Proof
