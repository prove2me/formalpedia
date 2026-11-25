-- Prove2me | solution 1 for BayesianPersuasion.Proof.fiber_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:11:06.341788+00:00
-- url     : https://prove2.me/submissions/018b4bc8-2c73-439d-96d6-f015e001c560

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_hull_compact

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
    BddAbove {z | (p.val, z) ∈ convexHull ℝ (bestReplyPayoffs u v)} := by
  apply (hull_compact u v hu hv).bddAbove_image continuous_snd.continuousOn |>.mono
  intro z hz
  exact ⟨(p.val, z), hz, rfl⟩
end BayesianPersuasion.Proof
