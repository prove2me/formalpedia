-- Prove2me | solution 1 for BayesianPersuasion.Proof.hull_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:11:44.58892+00:00
-- url     : https://prove2.me/submissions/f5a7058e-f051-4f26-8176-84d7624c422c

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_fiber_bddAbove

set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω]
open BayesianPersuasion.Proof
variable [TopologicalSpace A] [CompactSpace A] [Nonempty A] [T2Space A]
variable (u v : A → Ω → ℝ)
variable (hu : ∀ ω, Continuous (fun a => u a ω))
variable (hv : ∀ ω, Continuous (fun a => v a ω))
include hu hv
namespace BayesianPersuasion.Proof
theorem _root_.solution (p : Belief Ω) {z : ℝ}
    (hz : (p.val, z) ∈ convexHull ℝ (bestReplyPayoffs u v)) :
    z ≤ concavification u v p.val :=
  le_csSup (fiber_bddAbove u v hu hv p) hz
end BayesianPersuasion.Proof
