-- Prove2me | solution 1 for BayesianPersuasion.Proof.split_le_concavification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:12:29.889836+00:00
-- url     : https://prove2.me/submissions/732de8b2-82e5-4cb0-a55e-039e242ac8a0

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_hull_le
public import Theorems.Thm_BayesianPersuasion_Proof_split_pair_mem

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
theorem _root_.solution (p : Belief Ω) {n : ℕ} (w : Belief (Fin n))
    (b : Fin n → Belief Ω) (hb : BayesPlausible p w b) :
    splitValue u v w b ≤ concavification u v p.val :=
  hull_le u v hu hv p (split_pair_mem u v hu hv p w b hb)
end BayesianPersuasion.Proof
