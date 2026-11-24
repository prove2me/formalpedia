-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_unimod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:21.816848+00:00
-- url     : https://prove2.me/submissions/75ce672e-dd4b-4518-afcd-16898dab5a74

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_memI
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_invDiffSub

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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V)
    (hU : IsUnimodular h L) (y : V) :
    y ∈ dualI h L (invDiff K) ↔ y ∈ idealSmul (invDiffSub K) L := by
  have h10 : (1 : FractionalIdeal (RingOfIntegers K)⁰ K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) ∈ (1 : FractionalIdeal (RingOfIntegers K)⁰ K) :=
      (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
    rw [h0, FractionalIdeal.mem_zero_iff] at h1
    exact one_ne_zero h1
  have hne : majDualI K ≠ 0 := by
    first
    | exact FractionalIdeal.dual_ne_zero ℤ ℚ h10
    | exact FractionalIdeal.dual_ne_zero h10
  have hU' : dual h L = L := hU
  have hdual : ∀ x : V, x ∈ L ↔ ∀ z ∈ L, h z x ∈ (1 : Submodule (RingOfIntegers K) K) := by
    intro x
    conv_lhs => rw [← hU']
    simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
  have hD : ∀ x : V, x ∈ dualI h L (invDiff K) ↔
      ∀ z ∈ L, h z x ∈ (majDualI K : Submodule (RingOfIntegers K) K) := by
    intro x
    simp only [dualI, Set.mem_setOf_eq]
    exact forall₂_congr fun z _ => (majDual_memI (h z x)).symm
  rw [hD, majDual_invDiffSub]
  constructor
  · intro hy
    have hJ : ∀ d ∈ ((majDualI K)⁻¹ : FractionalIdeal (RingOfIntegers K)⁰ K), d • y ∈ L := by
      intro d hd
      rw [hdual]
      intro z hz
      rw [map_smul, smul_eq_mul, Submodule.mem_one]
      have hm : h z y * d ∈ majDualI K * (majDualI K)⁻¹ :=
        FractionalIdeal.mul_mem_mul (hy z hz) hd
      rw [mul_inv_cancel₀ hne, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨r, hr⟩ := hm
      exact ⟨r, by rw [hr, mul_comm]⟩
    have h1 : (1 : K) ∈ ((majDualI K : Submodule (RingOfIntegers K) K) *
        (((majDualI K)⁻¹ : FractionalIdeal (RingOfIntegers K)⁰ K) :
          Submodule (RingOfIntegers K) K)) := by
      rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hne]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
    have key : ∀ t ∈ ((majDualI K : Submodule (RingOfIntegers K) K) *
        (((majDualI K)⁻¹ : FractionalIdeal (RingOfIntegers K)⁰ K) :
          Submodule (RingOfIntegers K) K)),
        t • y ∈ idealSmul (majDualI K : Submodule (RingOfIntegers K) K) L := by
      intro t ht
      refine Submodule.mul_induction_on ht ?_ ?_
      · intro m hm n hn
        rw [mul_smul]
        exact Submodule.subset_span ⟨m, hm, n • y, hJ n hn, rfl⟩
      · intro a c ha hc
        rw [add_smul]
        exact Submodule.add_mem _ ha hc
    simpa using key 1 h1
  · intro hy
    unfold idealSmul at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      intro w hw
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 ((hdual x).1 hx w hw)
      rw [map_smul, smul_eq_mul, ← hr, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r ha
    | zero =>
      intro w _
      rw [map_zero]
      exact Submodule.zero_mem _
    | add a c _ _ ha hc =>
      intro w hw
      rw [map_add]
      exact Submodule.add_mem _ (ha w hw) (hc w hw)
    | smul r a _ ha =>
      intro w hw
      rw [← IsScalarTower.algebraMap_smul K r a, map_smul, smul_eq_mul, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r (ha w hw)
end Formalism.HermitianLatticesTheory
