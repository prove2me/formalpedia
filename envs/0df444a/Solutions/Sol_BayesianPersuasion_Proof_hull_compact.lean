-- Prove2me | solution 1 for BayesianPersuasion.Proof.hull_compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:10:25.132178+00:00
-- url     : https://prove2.me/submissions/d1c1bb60-056e-4f3d-9d25-515767b17d06

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_bestReplyPayoffs_compact
public import Theorems.Thm_BayesianPersuasion_Proof_compact_convexHull


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
theorem _root_.solution : IsCompact (convexHull ℝ (bestReplyPayoffs u v)) :=
  compact_convexHull (bestReplyPayoffs_compact u v hu hv)
end BayesianPersuasion.Proof
