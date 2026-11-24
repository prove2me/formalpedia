-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_tdual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:55.57969+00:00
-- url     : https://prove2.me/submissions/3be6839d-deca-4076-b3ab-197db3d1ac7f

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_star_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V) (y : V) :
    y ∈ tdual h L ↔ y ∈ dualI h L (invDiff K) := by
  simp only [tdual, dualI, invDiff, Set.mem_setOf_eq]
  constructor
  · intro hy x hx r
    have hr : IsIntegral ℤ (star (r : K)) := majDual_star_int r
    let r' : RingOfIntegers K := ⟨star (r : K), hr⟩
    have e : r' • x = (star (r : K)) • x := (IsScalarTower.algebraMap_smul K r' x).symm
    obtain ⟨z, hz⟩ := hy (r' • x) (L.smul_mem r' hx)
    refine ⟨z, ?_⟩
    rw [e, map_smulₛₗ h, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star] at hz
    rw [mul_comm]
    exact hz
  · intro hy x hx
    obtain ⟨z, hz⟩ := hy x hx 1
    refine ⟨z, ?_⟩
    have e1 : ((1 : RingOfIntegers K) : K) = 1 := rfl
    rw [e1, mul_one] at hz
    exact hz
end Formalism.HermitianLatticesTheory
