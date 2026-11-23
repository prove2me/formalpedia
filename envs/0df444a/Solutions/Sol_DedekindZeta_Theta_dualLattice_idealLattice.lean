-- Prove2me | solution 1 for DedekindZeta.Theta.dualLattice_idealLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:23:06.496044+00:00
-- url     : https://prove2.me/submissions/2d165e72-b5d2-4c9c-bc93-dbbdb9bb6e0e

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_dual_idealLattice
import Theorems.Thm_DedekindZeta_PoissonSummation_mem_dualLattice


set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    PoissonSummation.dualLattice (idealLattice K (𝔞 : FractionalIdeal (𝓞 K)⁰ K))
      = (idealLattice K (dualIdeal K 𝔞)).map
          ((conjMink K).toLinearEquiv.restrictScalars ℤ).toLinearMap := by
  refine Submodule.ext fun y => ?_
  rw [PoissonSummation.mem_dualLattice, Submodule.mem_map_equiv]
  -- `((conjMink K).toLinearEquiv.restrictScalars ℤ).symm y` equals `conjMink K y`
  -- since `conjMink` is an involution (`conjMink_symm_apply`); the underlying
  -- function is unchanged by `toLinearEquiv`/`restrictScalars`.
  have key : ((conjMink K).toLinearEquiv.restrictScalars ℤ).symm y = conjMink K y := by
    rw [← conjMink_symm_apply]; rfl
  rw [key, ← dual_idealLattice K 𝔞 hne y]
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · obtain ⟨k, hk⟩ := Submodule.mem_one.mp (h x hx)
    exact ⟨k, by simpa using hk.symm⟩
  · obtain ⟨k, hk⟩ := h x hx
    exact Submodule.mem_one.mpr ⟨k, by simpa using hk.symm⟩
end DedekindZeta.Theta
