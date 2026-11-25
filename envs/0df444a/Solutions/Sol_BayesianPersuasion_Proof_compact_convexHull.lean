-- Prove2me | solution 1 for BayesianPersuasion.Proof.compact_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:46.32185+00:00
-- url     : https://prove2.me/submissions/69660240-3350-400d-8c6f-ff906be940c8

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Theorems.Thm_BayesianPersuasion_Proof_convexHull_fixed_support

set_option autoImplicit true
@[expose] public section
public section
open Set Finset
open BayesianPersuasion BayesianPersuasion.Proof
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace E] [T2Space E] [ContinuousAdd E] [ContinuousSMul ℝ E]
namespace BayesianPersuasion.Proof
theorem _root_.solution {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  by_cases hne : s.Nonempty
  · letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
    let F : Belief (Fin (Module.finrank ℝ E + 1)) ×
        (Fin (Module.finrank ℝ E + 1) → s) → E := fun t => ∑ j, t.1.val j • (t.2 j).val
    have hF : Continuous F := by
      unfold F
      exact continuous_finsetSum _ fun j _ =>
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd))
    have heq : convexHull ℝ s = Set.range F := by
      ext x
      constructor
      · intro hx
        obtain ⟨w, z, hz⟩ := convexHull_fixed_support hne hx
        exact ⟨(w, z), hz⟩
      · rintro ⟨⟨w, z⟩, rfl⟩
        exact mem_convexHull_of_exists_fintype w.val (fun j => (z j).val)
          w.property.1 w.property.2 (fun j => (z j).property) rfl
    rw [heq]
    exact isCompact_range hF
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, convexHull_empty]
    exact isCompact_empty
end BayesianPersuasion.Proof
