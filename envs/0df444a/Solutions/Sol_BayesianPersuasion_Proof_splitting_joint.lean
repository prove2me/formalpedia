-- Prove2me | solution 1 for BayesianPersuasion.Proof.splitting_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:01:07.762166+00:00
-- url     : https://prove2.me/submissions/b2f1f21c-516d-4b88-85ec-6c95c7bb1bd8

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_Signals

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
    (ω : Ω) (s : Fin n) :
    p.val ω * (splittingSignal p hp w b hb ω).val s = w.val s * (b s).val ω := by
  change p.val ω * (w.val s * (b s).val ω / p.val ω) = _
  field_simp [ne_of_gt (hp ω)]
end BayesianPersuasion.Proof
