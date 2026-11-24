-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locDual_dualAt_loc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:10.355799+00:00
-- url     : https://prove2.me/submissions/e9140ed1-1b64-449c-8fcb-b63bd5ab406e

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_dualAt
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_locR
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_h_smul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_dualAt_anti
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_sigma_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (L : Submodule R V) :
    dualAt h p (loc (K := K) p L) = dualAt h p L := by
  apply le_antisymm
  · apply locDual_dualAt_anti
    intro y hy
    show ∃ s ∈ hcompl (K := K) p, s • y ∈ L
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hy⟩
  · intro x hx
    rw [locDual_mem_dualAt] at hx ⊢
    intro y hy
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ hcompl (K := K) p, s • y ∈ L := hy
    have h1 := hx _ hsy
    rw [locDual_h_smul_left, locDual_mem_locR] at h1
    obtain ⟨t, ht, hty⟩ := h1
    rw [locDual_mem_locR]
    refine ⟨t * locBasic_sigma hinj hstar s,
      Submonoid.mul_mem _ ht (locDual_sigma_mem hinj hstar p s hs), ?_⟩
    have spec : algebraMap R K (locBasic_sigma hinj hstar s) = star (algebraMap R K s) :=
      (hstar s).choose_spec
    rw [map_mul, spec, mul_assoc]
    exact hty
end Formalism.HermitianLatticesTheory
