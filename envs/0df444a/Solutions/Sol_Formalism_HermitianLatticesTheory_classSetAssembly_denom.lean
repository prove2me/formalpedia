-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:43:18.801829+00:00
-- url     : https://prove2.me/submissions/66cc1d61-1968-458b-91a1-ab5164428e83

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_qsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_sum_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_coord_zero
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (u : Fin n → V) (hu : LinearIndependent ℝ (ι ∘ u)) (d : ℕ) (hd : 0 < d)
    (hint : ∀ i j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) = z) :
    ∃ e : ℤ, e ≠ 0 ∧ ∀ x : V, (∀ j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h x (u j)) = z) →
      e • x ∈ AddSubgroup.closure (Set.range u) := by
  obtain ⟨M, hM⟩ : ∃ M : Fin n → Fin n → ℤ,
      ∀ i j, (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) = M i j := by
    choose M hM using ‹∀ i j, ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) = z›
    exact ⟨M, hM⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin n) (Fin n) ℚ,
      A = (Int.castRingHom ℚ).mapMatrix (Matrix.of M) := ⟨_, rfl⟩
  have hA : ∀ i j, A i j = (d : ℚ) * Algebra.trace ℚ K (h (u i) (u j)) := fun i j => by
    rw [hAdef, hM i j]
    simp
  have hdetA : A.det = (((Matrix.of M).det : ℤ) : ℚ) := by
    rw [hAdef, ← RingHom.map_det]
    simp
  have hadj : A.adjugate = (Int.castRingHom ℚ).mapMatrix (Matrix.of M).adjugate := by
    rw [hAdef, RingHom.map_adjugate]
  have hdet : (Matrix.of M).det ≠ 0 := by
    intro h0
    have hA0 : A.det = 0 := by rw [hdetA, h0, Int.cast_zero]
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hA0
    have hr := classSetAssembly_coord_zero h hpos ι hι u hu (fun i => (d : ℚ) * v i)
      (fun j => by
        have e := congrFun hv j
        simp only [Matrix.vecMul, dotProduct, hA, Pi.zero_apply] at e
        rw [← e]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring)
    apply hv0
    funext i
    have e := congrFun hr i
    simp only [Pi.zero_apply] at e
    exact (mul_eq_zero.mp e).resolve_left (by exact_mod_cast hd.ne')
  refine ⟨(Matrix.of M).det, hdet, fun x hx => ?_⟩
  choose w hw using hx
  obtain ⟨t, ht⟩ := classSetAssembly_span h hpos ι hι u hu x
  have hvec : Matrix.vecMul t A = fun j => ((w j : ℤ) : ℚ) := by
    funext j
    rw [← hw j, ht, classSetAssembly_tr_sum_left, Finset.mul_sum]
    simp only [Matrix.vecMul, dotProduct, hA]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [classSetAssembly_tr_qsmul_left]
    ring
  have hkey : A.det • t = Matrix.vecMul (fun j => ((w j : ℤ) : ℚ)) A.adjugate := by
    rw [← hvec, Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul,
      Matrix.vecMul_one]
  set z : Fin n → ℤ := Matrix.vecMul w (Matrix.of M).adjugate with hzdef
  have hz : ∀ i, ((z i : ℤ) : ℚ) = (((Matrix.of M).det : ℤ) : ℚ) * t i := by
    intro i
    have e := congrFun hkey i
    rw [Pi.smul_apply, smul_eq_mul, hdetA, hadj] at e
    rw [e, hzdef]
    simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply]
    push_cast
    rfl
  have hx' : (Matrix.of M).det • x = ∑ i, z i • u i := by
    rw [ht, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K, smul_smul]
    congr 1
    have e := congrArg (fun q : ℚ => (q : K)) (hz i)
    simp only [Rat.cast_mul, Rat.cast_intCast] at e
    exact e.symm
  rw [hx']
  exact sum_mem fun i _ => zsmul_mem (AddSubgroup.subset_closure (Set.mem_range_self i)) _
end Formalism.HermitianLatticesTheory
