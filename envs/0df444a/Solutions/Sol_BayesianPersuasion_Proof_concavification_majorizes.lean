-- Prove2me | solution 1 for BayesianPersuasion.Proof.concavification_majorizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:12:30.311372+00:00
-- url     : https://prove2.me/submissions/43bce08d-e249-4a5c-a5e0-740fa09234ed

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_sender_pair_mem
public import Theorems.Thm_BayesianPersuasion_Proof_hull_le

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
theorem _root_.solution (p : Belief Ω) :
    senderPayoff u v p ≤ concavification u v p.val :=
  hull_le u v hu hv p (subset_convexHull ℝ _ (sender_pair_mem u v hu hv p))
end BayesianPersuasion.Proof
