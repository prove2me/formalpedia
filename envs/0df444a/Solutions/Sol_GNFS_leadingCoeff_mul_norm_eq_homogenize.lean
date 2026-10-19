-- Prove2me | solution 1 for GNFS.leadingCoeff_mul_norm_eq_homogenize
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:59:55.382362+00:00
-- url     : https://prove2.me/submissions/abe43bc1-d2ab-417e-80f1-d3d7a62df256

import Mathlib
import Definitions.Def_GNFS_defs
open Polynomial IntermediateField GNFS

theorem solution (f : ℤ[X])
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (θ : ℂ) (hθ : aeval θ f = 0) (a b : ℤ) :
    (f.leadingCoeff : ℚ) *
        Algebra.norm ℚ ((a : ℚ⟮θ⟯) - (b : ℚ⟮θ⟯) * AdjoinSimple.gen ℚ θ) =
      (homogenize f a b : ℚ) := by
  set fq := f.map (Int.castRingHom ℚ) with hfq
  have hfq0 : fq ≠ 0 := hf.ne_zero
  have hθq : aeval θ fq = 0 := by
    rw [hfq, ← algebraMap_int_eq, aeval_map_algebraMap]; exact hθ
  have hint : IsIntegral ℚ θ := ⟨fq * C fq.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hfq0, by
    rw [eval₂_mul, eval₂_C]
    have : eval₂ (algebraMap ℚ ℂ) θ fq = 0 := hθq
    rw [this, zero_mul]⟩
  have hdeg : fq.natDegree = f.natDegree := natDegree_map_eq_of_injective
    (RingHom.injective_int _) f
  have hlc : fq.leadingCoeff = (f.leadingCoeff : ℚ) := by
    rw [hfq, leadingCoeff_map_of_injective (RingHom.injective_int _)]; rfl
  have hmin : fq * C fq.leadingCoeff⁻¹ = minpoly ℚ θ := minpoly.eq_of_irreducible hf hθq
  set pb := adjoin.powerBasis hint
  have hgen : pb.gen = AdjoinSimple.gen ℚ θ := adjoin.powerBasis_gen hint
  have hfin : Module.finrank ℚ ℚ⟮θ⟯ = f.natDegree := by
    rw [adjoin.finrank hint, ← hmin, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hfq0)),
      hdeg]
  have : Module.Finite ℚ ℚ⟮θ⟯ := pb.finite
  -- characteristic polynomial of multiplication by the generator
  have hchar : (Algebra.lmul ℚ ℚ⟮θ⟯ (AdjoinSimple.gen ℚ θ)).charpoly = minpoly ℚ θ := by
    have h1 := charpoly_leftMulMatrix pb
    rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, hgen, minpoly_gen] at h1
    exact h1
  set g := AdjoinSimple.gen ℚ θ
  set L := Algebra.lmul ℚ ℚ⟮θ⟯ g
  have hlmul : Algebra.lmul ℚ ℚ⟮θ⟯ ((a : ℚ⟮θ⟯) - (b : ℚ⟮θ⟯) * g) =
      algebraMap ℚ _ (a : ℚ) - (b : ℚ) • L := by
    ext y
    simp [L, Algebra.smul_def, mul_assoc]
  rw [Algebra.norm_apply, hlmul]
  have hF : (GNFS.homogenize f a b : ℚ) = ∑ i ∈ Finset.range (f.natDegree + 1),
      (f.coeff i : ℚ) * (a : ℚ) ^ i * (b : ℚ) ^ (f.natDegree - i) := by
    unfold GNFS.homogenize; push_cast; rfl
  rw [hF]
  by_cases hb : b = 0
  · subst hb
    simp only [Int.cast_zero, zero_smul, sub_zero]
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.det_smul, map_one, mul_one, hfin]
    rw [Finset.sum_eq_single f.natDegree]
    · rw [Nat.sub_self, pow_zero, mul_one, Polynomial.leadingCoeff]
    · intro i hi hne
      have : 0 < f.natDegree - i := by
        have := Finset.mem_range.mp hi; omega
      rw [zero_pow this.ne', mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
  · have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have hsplit : algebraMap ℚ (Module.End ℚ ℚ⟮θ⟯) (a : ℚ) - (b : ℚ) • L =
        (b : ℚ) • (algebraMap ℚ (Module.End ℚ ℚ⟮θ⟯) ((a : ℚ) / b) - L) := by
      rw [smul_sub, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul,
        mul_div_cancel₀ _ hbq]
    rw [hsplit, LinearMap.det_smul, ← LinearMap.eval_charpoly, hchar, ← hmin, hfin, eval_mul,
      eval_C, eval_eq_sum_range, hdeg, hlc]
    have hlc0 : (f.leadingCoeff : ℚ) ≠ 0 := by
      rw [← hlc]; exact leadingCoeff_ne_zero.mpr hfq0
    have hcan : ∀ S : ℚ, (f.leadingCoeff : ℚ) * ((b : ℚ) ^ f.natDegree * (S * (f.leadingCoeff : ℚ)⁻¹))
        = (b : ℚ) ^ f.natDegree * S := fun S => by field_simp
    rw [hcan, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ f.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hfq, coeff_map, eq_intCast, div_pow]
    have hpow : (b : ℚ) ^ f.natDegree = (b : ℚ) ^ i * (b : ℚ) ^ (f.natDegree - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hi']
    rw [hpow]
    field_simp
