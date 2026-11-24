-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_zdual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:22.133982+00:00
-- url     : https://prove2.me/submissions/2b0a2e78-944f-48d5-9693-0914185e25fc

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_inner
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_mem_zmap
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDualJ_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_jW_jW

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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
variable [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution [IsTotallyComplex K] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    (hX : ∀ v, IsFrame h b v (X v)) (L : Submodule (RingOfIntegers K) V)
    [DiscreteTopology (zmap (realize b X) L)] [IsZLattice ℝ (zmap (realize b X) L)]
    (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    w ∈ Formalism.HadamardInequality.zdual (zmap (realize b X) L) ↔
      ∃ y : V, (∀ x ∈ L, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = 2 * z) ∧
        w = jW h b X (realize b X y) := by
  classical
  have hinner := majDual_inner h b X hst hX
  have hmemZ : ∀ u, u ∈ Formalism.HadamardInequality.zdual (zmap (realize b X) L) ↔
      ∀ x ∈ zmap (realize b X) L, ∃ z : ℤ, inner ℝ x u = z := fun u => Iff.rfl
  constructor
  swap
  · rintro ⟨y, hy, rfl⟩
    rw [hmemZ]
    intro x hx
    obtain ⟨x', hx', rfl⟩ := (majDual_mem_zmap (realize b X) L x).1 hx
    obtain ⟨z, hz⟩ := hy x' hx'
    refine ⟨z, ?_⟩
    rw [hinner, hz]
    (try push_cast) <;> ring
  intro hw
  rw [hmemZ] at hw
  set bZ := Module.Free.chooseBasis ℤ (zmap (realize b X) L) with hbZ
  set bb := bZ.ofZLatticeBasis ℝ (zmap (realize b X) L) with hbb
  have hbbΛ : ∀ i, bb i ∈ zmap (realize b X) L := fun i => by
    rw [hbb, Module.Basis.ofZLatticeBasis_apply]
    exact (bZ i).2
  have hm : ∀ i, ∃ m ∈ L, realize b X m = bb i := fun i =>
    (majDual_mem_zmap (realize b X) L (bb i)).1 (hbbΛ i)
  choose m hmL hmR using hm
  have hext : ∀ p q : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2),
      (∀ i, inner ℝ (bb i) p = inner ℝ (bb i) q) → p = q := by
    intro p q hpq
    apply ext_inner_left ℝ
    intro u
    rw [← bb.sum_repr u, sum_inner, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, real_inner_smul_left, hpq i]
  set Gq : Matrix (Module.Free.ChooseBasisIndex ℤ (zmap (realize b X) L))
    (Module.Free.ChooseBasisIndex ℤ (zmap (realize b X) L)) ℚ :=
    Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k)) / 2 with hGq
  have hGr : ∀ i k, inner ℝ (bb i) (jW h b X (bb k)) = (Gq i k : ℝ) := by
    intro i k
    rw [← hmR i, ← hmR k, hinner, hGq, Matrix.of_apply]
    (try push_cast) <;> ring
  have hdet : Gq.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    set u := ∑ k, (v k : ℝ) • bb k with hu
    have hJu : jW h b X u = 0 := by
      apply hext
      intro i
      rw [inner_zero_right, ← majDualJ_apply, hu, map_sum, inner_sum]
      simp only [map_smul, real_inner_smul_right, majDualJ_apply, hGr]
      have h1 := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
      have h2 : ((∑ k, Gq i k * v k : ℚ) : ℝ) = 0 := by
        rw [h1]
        simp
      push_cast at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hu0 : u = 0 := by
      rw [← majDual_jW_jW h b X hX u, hJu, ← majDualJ_apply, map_zero]
    apply hv0
    have hli := bb.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    funext k
    have h3 := hli (fun k => (v k : ℝ)) (hu.symm.trans hu0) k
    simp only [Pi.zero_apply]
    exact_mod_cast h3
  have hn : ∀ i, ∃ z : ℤ, inner ℝ (bb i) w = z := fun i => hw (bb i) (hbbΛ i)
  choose nz hnz using hn
  set qv := Matrix.mulVec Gq⁻¹ (fun i => (nz i : ℚ)) with hqv
  set y : V := ∑ k, (algebraMap ℚ K (qv k)) • m k with hy
  have htr : ∀ x : V, Algebra.trace ℚ K (h x y) =
      ∑ k, qv k * Algebra.trace ℚ K (h x (m k)) := by
    intro x
    rw [hy, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have hq : ∀ i, Algebra.trace ℚ K (h (m i) y) / 2 = nz i := by
    intro i
    have e1 : Matrix.mulVec Gq qv = fun i => (nz i : ℚ) := by
      rw [hqv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Gq (isUnit_iff_ne_zero.mpr hdet),
        Matrix.one_mulVec]
    have e2 := congrFun e1 i
    simp only [Matrix.mulVec, dotProduct] at e2
    rw [← e2, htr, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hGq, Matrix.of_apply]
    ring
  have hwy : w = jW h b X (realize b X y) := by
    apply hext
    intro i
    rw [hnz i, ← hmR i, hinner]
    have e3 := congrArg (fun q : ℚ => (q : ℝ)) (hq i)
    push_cast at e3
    exact e3.symm
  refine ⟨y, ?_, hwy⟩
  intro x hx
  obtain ⟨z, hz⟩ := hw (realize b X x) ((majDual_mem_zmap (realize b X) L _).2 ⟨x, hx, rfl⟩)
  refine ⟨z, ?_⟩
  rw [hwy, hinner] at hz
  have e4 : ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ) = ((2 * z : ℚ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast e4
end Formalism.HermitianLatticesTheory
