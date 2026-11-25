-- Prove2me | solution 1 for BayesianPersuasion.Proof.bestReplyPayoffs_compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:40.76598+00:00
-- url     : https://prove2.me/submissions/2c96cc77-8908-4b66-bb98-0328d327e4f6

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_bestReply_graph_isClosed
public import Theorems.Thm_BayesianPersuasion_Proof_continuous_expected


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
theorem _root_.solution : IsCompact (bestReplyPayoffs u v) := by
  apply (bestReply_graph_isClosed u hu).isCompact.image
  exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_expected v hv)
end BayesianPersuasion.Proof
