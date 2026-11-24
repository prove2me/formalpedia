-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.exists_orth_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:35:27.787824+00:00
-- url     : https://prove2.me/submissions/e3367f68-3f28-41f4-b523-c31cb4cffb33

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_TransvectionIsometry
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ExistsSumOfMemSpanImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.LatticeBaseChangeAlt
open Finset
section aux
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
private theorem exists_orth_decomp_of_finiteDimensional (K : Submodule ℝ V) [FiniteDimensional ℝ K]
    (a : V) : ∃ w ∈ K, ∃ z : V, (∀ p ∈ K, inner ℝ p z = 0) ∧ a = w + z := by
  have : CompleteSpace K := FiniteDimensional.complete ℝ K
  obtain ⟨w, hw, z, hz, h⟩ : ∃ w ∈ K, ∃ z ∈ K.orthogonal, a = w + z := by
    exact K.exists_add_mem_mem_orthogonal a
  refine ⟨w, hw, z, fun p hp => ?_, h⟩
  exact Submodule.inner_right_of_mem_orthogonal hp hz
end aux
end Formalism.LatticeBaseChangeAlt
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution {ι : Type*} (v : ι → V) (T : Finset ι) (a : V) :
    ∃ w ∈ Submodule.span ℝ (v '' (T : Set ι)), ∃ z : V,
      (∀ p ∈ Submodule.span ℝ (v '' (T : Set ι)), inner ℝ p z = 0) ∧ a = w + z ∧
        ‖z‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  have : FiniteDimensional ℝ (Submodule.span ℝ (v '' (T : Set ι))) :=
    FiniteDimensional.span_of_finite ℝ (T.finite_toSet.image v)
  obtain ⟨w, hw, z, hz, hwz⟩ :=
    exists_orth_decomp_of_finiteDimensional (Submodule.span ℝ (v '' (T : Set ι))) a
  refine ⟨w, hw, z, hz, hwz, ?_⟩
  rw [hwz, norm_add_sq_real, hz w hw]
  nlinarith [sq_nonneg ‖w‖]
end Formalism.LatticeBaseChangeAlt
