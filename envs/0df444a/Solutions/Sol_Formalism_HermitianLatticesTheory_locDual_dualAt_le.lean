-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locDual_dualAt_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:47.319696+00:00
-- url     : https://prove2.me/submissions/c0d03fde-a80d-472e-ada1-23fa74be6c90

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_dualAt
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_locR
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_h_smul_right
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_h_smul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_one_mul
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_alg_mem
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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (L : Submodule R V) (hL : L.FG) :
    dualAt h p L ≤ loc (K := K) p (dual h L) := by
  classical
  intro x hx
  rw [locDual_mem_dualAt] at hx
  obtain ⟨t, rfl⟩ := hL
  have hloc : ∀ y ∈ t, ∃ s ∈ hcompl (K := K) p,
      algebraMap R K s * h y x ∈ (1 : Submodule R K) :=
    fun y hy => (locDual_mem_locR p _).mp (hx y (Submodule.subset_span hy))
  choose! s hs hsy using hloc
  refine ⟨∏ y ∈ t, s y, Submonoid.prod_mem _ (fun y hy => hs y hy), ?_⟩
  rw [mem_dual_iff_forall_mem_one]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [locDual_h_smul_right, ← Finset.mul_prod_erase t s hy, map_mul,
      mul_comm (algebraMap R K (s y)), mul_assoc]
    exact locDual_one_mul (locDual_alg_mem _) (hsy y hy)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [locDual_h_smul_left]
    obtain ⟨u, hu⟩ := hstar r
    rw [← hu]
    exact locDual_one_mul (locDual_alg_mem u) hy
end Formalism.HermitianLatticesTheory
