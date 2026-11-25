-- Prove2me | solution 1 for BayesianPersuasion.Proof.concavification_concave
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:12:31.102796+00:00
-- url     : https://prove2.me/submissions/e5cfd49e-bd64-4e69-9ab1-b879ab1f7a5d

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_hull_le
public import Theorems.Thm_BayesianPersuasion_Proof_concavification_max_point
public import Theorems.Thm_BayesianPersuasion_Proof_probabilitySimplex_convex

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
theorem _root_.solution :
    ConcaveOn ℝ (probabilitySimplex Ω) (concavification u v) := by
  refine ⟨probabilitySimplex_convex, ?_⟩
  intro p hp q hq a b ha hb hab
  let P : Belief Ω := ⟨p, hp⟩
  let Q : Belief Ω := ⟨q, hq⟩
  let R : Belief Ω := ⟨a • p + b • q, probabilitySimplex_convex hp hq ha hb hab⟩
  have h := convex_convexHull ℝ (bestReplyPayoffs u v)
    (concavification_max_point u v hu hv P)
    (concavification_max_point u v hu hv Q) ha hb hab
  exact hull_le u v hu hv R h
end BayesianPersuasion.Proof
