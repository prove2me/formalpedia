-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.invariant_kernel_trace_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:05:13.695735+00:00
-- url     : https://prove2.me/submissions/626f5bf5-0386-4f49-8753-6cae4218d00c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
open Module Finset Matrix
namespace Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
theorem _root_.solution : Formalism.HermitianLattices.RamifiedLatticeOperators.InvariantKernelTraceVanishes := by
  intro F _ _ _ r R _ k φ hk hnm
  classical
  set s := univ.filter (fun f : Fin r → F => f ≠ 0) with hs
  let g : (Fin r → F) → Set (Fin r → F) := fun f => MulAction.orbit Fˣ f
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image g) (g := g)
    (fun i hi => Finset.mem_image_of_mem g hi)]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.mp hj
  have hf0' : f0 ≠ 0 := (Finset.mem_filter.mp hf0).2
  have key : ∑ i ∈ s with g i = g f0, k i * φ i = ∑ c : Fˣ, k ((c : F) • f0) * φ ((c : F) • f0) := by
    symm
    refine Finset.sum_bij (fun c _ => (c : F) • f0) ?_ ?_ ?_ ?_
    · intro c _
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · exact smul_ne_zero (Units.ne_zero c) hf0'
      · show MulAction.orbit Fˣ ((c : F) • f0) = MulAction.orbit Fˣ f0
        rw [← Units.smul_def]; exact MulAction.orbit_smul c f0
    · intro c _ c' _ h
      have h2 : ((c : F) - c') • f0 = 0 := by rw [sub_smul, h, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact Units.ext (sub_eq_zero.mp h3)
      · exact absurd h3 hf0'
    · intro i hi
      have hi2 : MulAction.orbit Fˣ i = MulAction.orbit Fˣ f0 := (Finset.mem_filter.mp hi).2
      have hi3 : i ∈ MulAction.orbit Fˣ f0 := hi2 ▸ MulAction.mem_orbit_self i
      obtain ⟨c, hc⟩ := hi3
      exact ⟨c, Finset.mem_univ _, by rw [← hc]; exact (Units.smul_def c f0).symm⟩
    · intro c _; rfl
  rw [key]
  have : ∑ c : Fˣ, k ((c : F) • f0) * φ ((c : F) • f0) = k f0 * Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP φ f0 := by
    rw [Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hk c f0]; rfl
  rw [this, hnm f0 hf0', mul_zero]
end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
