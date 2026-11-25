-- Prove2me | solution 1 for BayesianPersuasion.Proof.continuous_expected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:57:49.620741+00:00
-- url     : https://prove2.me/submissions/f14a6f49-4406-4678-9ab2-9ea591852105

module
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BayesianPersuasion_Primitives

set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable (Ω : Type uΩ) [Fintype Ω]
variable {Ω} {A : Type uA}
open BayesianPersuasion.Proof
variable [TopologicalSpace A]
namespace BayesianPersuasion.Proof
theorem _root_.solution (u : A → Ω → ℝ) (hu : ∀ ω, Continuous (fun a => u a ω)) :
    Continuous (fun x : Belief Ω × A => expected u x.1 x.2) := by
  unfold expected
  exact continuous_finsetSum _ fun ω _ =>
    ((continuous_apply ω).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((hu ω).comp continuous_snd)
end BayesianPersuasion.Proof
