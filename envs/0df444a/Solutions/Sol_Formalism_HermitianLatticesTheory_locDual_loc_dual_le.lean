-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locDual_loc_dual_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:47.57887+00:00
-- url     : https://prove2.me/submissions/506ecc07-4263-4af6-9cc5-e871c4f68dcb

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_dualAt
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_locR
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_h_smul_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HermitianLatticesTheory
section SlopeTestRemainingChoices
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
private theorem mem_dual_iff_forall_mem_one (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]
end SlopeTestRemainingChoices
end Formalism.HermitianLatticesTheory
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) :
    loc (K := K) p (dual h L) ≤ dualAt h p L := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ hcompl (K := K) p, s • x ∈ dual h L := hx
  rw [mem_dual_iff_forall_mem_one] at hsx
  rw [locDual_mem_dualAt]
  intro y hy
  rw [locDual_mem_locR]
  refine ⟨s, hs, ?_⟩
  rw [← locDual_h_smul_right]
  exact hsx y hy
end Formalism.HermitianLatticesTheory
