-- Prove2me | solution 1 for EntanglingOps.BinaryPhase.eq_6_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:24:11.106977+00:00
-- url     : https://prove2.me/submissions/ad8dc7fc-bcd8-4354-ab87-89a5e61b5258

import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

open Matrix
open scoped Kronecker
open EntanglingOps.BinaryPhase

lemma conj_vecMulVec {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix κ ι ℂ) (u : ι → ℂ) :
    M * vecMulVec u (star u) * Mᴴ = vecMulVec (M *ᵥ u) (star (M *ᵥ u)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

lemma projPair_eq (d : ℕ) : reindex (regroup d) (regroup d) (projPhi d ⊗ₖ projPhi d) =
    vecMulVec (fun p : (Fin d × Fin d) × (Fin d × Fin d) => phiVec d (p.1.1, p.2.1) * phiVec d (p.1.2, p.2.2))
      (star (fun p : (Fin d × Fin d) × (Fin d × Fin d) => phiVec d (p.1.1, p.2.1) * phiVec d (p.1.2, p.2.2))) := by
  ext ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩ ⟨⟨c1, e1⟩, ⟨c2, e2⟩⟩
  simp [projPhi, vecMulVec, regroup, Matrix.kroneckerMap_apply]
  ring

lemma phi_prod (d : ℕ) (m c : Fin d × Fin d) :
    phiVec d (m.1, c.1) * phiVec d (m.2, c.2) = if m = c then ((d : ℂ))⁻¹ else 0 := by
  obtain ⟨m1, m2⟩ := m
  obtain ⟨c1, c2⟩ := c
  have h : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = d := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]; simp
  by_cases h1 : m1 = c1 <;> by_cases h2 : m2 = c2 <;> simp [phiVec, h1, h2]
  rw [← mul_inv, h]

lemma vk_eq (d : ℕ) (O : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ((O ⊗ₖ (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) *ᵥ
      (fun p : (Fin d × Fin d) × (Fin d × Fin d) => phiVec d (p.1.1, p.2.1) * phiVec d (p.1.2, p.2.2))) =
      fun p => (d : ℂ)⁻¹ * O p.1 p.2 := by
  funext ⟨r, c⟩
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.kroneckerMap_apply]
  rw [Fintype.sum_eq_single c (fun m1 hm1 => Finset.sum_eq_zero (fun m2 _ => by
    rw [phi_prod, Matrix.one_apply]; split_ifs <;> simp_all))]
  rw [Fintype.sum_eq_single c (fun m2 hm2 => by
    rw [phi_prod, Matrix.one_apply]; split_ifs <;> simp_all)]
  rw [phi_prod, if_pos rfl, Matrix.one_apply_eq, mul_one, mul_comm]

lemma E_eq (d : ℕ) {κ : Type} [Fintype κ] (O : κ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    reindex (regroup d) (regroup d) (choiOp O) =
      ∑ k, vecMulVec (fun p => (d : ℂ)⁻¹ * O k p.1 p.2) (star (fun p => (d : ℂ)⁻¹ * O k p.1 p.2)) := by
  unfold choiOp
  rw [projPair_eq]
  simp_rw [conj_vecMulVec, vk_eq]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]

lemma ptr_sum {a b ι : Type} [Fintype b] (s : Finset ι) (X : ι → Matrix (a × b) (a × b) ℂ) :
    WildeQIT.partialTraceRight (∑ k ∈ s, X k) = ∑ k ∈ s, WildeQIT.partialTraceRight (X k) := by
  ext i j
  simp only [WildeQIT.partialTraceRight, Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.sum_comm]

lemma part8_single (d : ℕ) (hd : 0 < d) (O : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    O * ρ * Oᴴ = ((d : ℂ) ^ 2) • WildeQIT.partialTraceRight
        (vecMulVec (fun p => (d : ℂ)⁻¹ * O p.1 p.2) (star (fun p => (d : ℂ)⁻¹ * O p.1 p.2)) *
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρᵀ)) := by
  ext r r'
  simp only [WildeQIT.partialTraceRight, Matrix.smul_apply, Matrix.of_apply, Matrix.mul_apply]
  have inner : ∀ c, ∑ m, vecMulVec (fun p => (d : ℂ)⁻¹ * O p.1 p.2) (star (fun p => (d : ℂ)⁻¹ * O p.1 p.2)) (r, c) m *
      ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρᵀ) m (r', c) =
      ∑ m2, ((d : ℂ)⁻¹ * O r c) * star ((d : ℂ)⁻¹ * O r' m2) * ρ c m2 := by
    intro c
    rw [Fintype.sum_prod_type, Fintype.sum_eq_single r' (fun m1 hm1 => Finset.sum_eq_zero (fun m2 _ => by
      rw [Matrix.kroneckerMap_apply, Matrix.one_apply, if_neg hm1, zero_mul, mul_zero]))]
    refine Finset.sum_congr rfl (fun m2 _ => ?_)
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul, Matrix.transpose_apply,
      vecMulVec_apply]
    rfl
  rw [Finset.sum_congr rfl (fun c _ => inner c), Finset.sum_comm, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m2 _ => ?_)
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Matrix.conjTranspose_apply, star_mul', star_inv₀, Complex.star_def, Complex.conj_natCast]
  field_simp

theorem part8 (d : ℕ) (hd : 0 < d) {κ : Type} [Fintype κ]
    (O : κ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    krausMap O ρ = ((d : ℂ) ^ 2) • WildeQIT.partialTraceRight
        (reindex (regroup d) (regroup d) (choiOp O) *
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρᵀ)) := by
  rw [E_eq, Finset.sum_mul, ptr_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun k _ => part8_single d hd (O k) ρ)

lemma sqrt_inv_four (d : ℕ) :
    ((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹ * (((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹) =
      ((d : ℂ) ^ 2)⁻¹ := by
  have h : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = d := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]; simp
  rw [← mul_inv, ← mul_inv, h]; ring

lemma projPhiPair_apply (d : ℕ) (u v u' v' : Fin d × Fin d) :
    projPhiPair d (u, v) (u', v') = if u = v ∧ u' = v' then ((d : ℂ) ^ 2)⁻¹ else 0 := by
  obtain ⟨a2, b2⟩ := u
  obtain ⟨a3, b3⟩ := v
  obtain ⟨a2', b2'⟩ := u'
  obtain ⟨a3', b3'⟩ := v'
  simp only [projPhiPair, regroup, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.prodProdProdComm_symm, Equiv.prodProdProdComm_apply, Matrix.kroneckerMap_apply,
    projPhi, vecMulVec_apply, Pi.star_apply, phiVec, Prod.mk.injEq]
  by_cases h1 : a2 = a3 <;> by_cases h2 : b2 = b3 <;> by_cases h3 : a2' = a3' <;>
    by_cases h4 : b2' = b3' <;> simp [h1, h2, h3, h4, Complex.conj_ofReal]
  exact sqrt_inv_four d

theorem eq7_thm (d : ℕ) (hd : 0 < d) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ((d : ℂ) ^ 2) • WildeQIT.partialTraceRight
      (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρ) * projPhiPair d) = ρᵀ := by
  ext i j
  simp only [WildeQIT.partialTraceRight, Matrix.smul_apply, Matrix.of_apply, Matrix.mul_apply]
  rw [Fintype.sum_eq_single j (fun k hk => Finset.sum_eq_zero (fun m _ => by
    obtain ⟨m1, m2⟩ := m
    rw [projPhiPair_apply, if_neg (by tauto), mul_zero]))]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single i (fun m1 hm1 => Finset.sum_eq_zero (fun m2 _ => by
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply, if_neg (Ne.symm hm1), zero_mul, zero_mul]))]
  rw [Fintype.sum_eq_single i (fun m2 hm2 => by
    rw [projPhiPair_apply, if_neg (by tauto), mul_zero])]
  rw [projPhiPair_apply, if_pos ⟨rfl, rfl⟩, Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
    one_mul, Matrix.transpose_apply, smul_eq_mul]
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

lemma ptr_smul {a b : Type} [Fintype b] (c : ℂ) (X : Matrix (a × b) (a × b) ℂ) :
    WildeQIT.partialTraceRight (c • X) = c • WildeQIT.partialTraceRight X := by
  ext i j
  simp only [WildeQIT.partialTraceRight, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma ptr_assoc {T : Type} [Fintype T] [DecidableEq T] (E X : Matrix (T × T) (T × T) ℂ) :
    WildeQIT.partialTraceRight
        (reindex (Equiv.prodAssoc T T T) (Equiv.prodAssoc T T T) (E ⊗ₖ (1 : Matrix T T ℂ)) *
          ((1 : Matrix T T ℂ) ⊗ₖ X)) =
      WildeQIT.partialTraceRight (E * ((1 : Matrix T T ℂ) ⊗ₖ WildeQIT.partialTraceRight X)) := by
  ext r r'
  simp only [WildeQIT.partialTraceRight, Matrix.of_apply, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have h1 : ∀ v, ∑ m : T × (T × T), reindex (Equiv.prodAssoc T T T) (Equiv.prodAssoc T T T)
      (E ⊗ₖ (1 : Matrix T T ℂ)) (r, (u, v)) m * ((1 : Matrix T T ℂ) ⊗ₖ X) m (r', (u, v)) =
      ∑ m2, E (r, u) (r', m2) * X (m2, v) (u, v) := by
    intro v
    rw [Fintype.sum_prod_type, Fintype.sum_eq_single r' (fun m1 hm1 => Finset.sum_eq_zero (fun m _ => by
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply, if_neg hm1]; ring))]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun m2 _ => ?_)
    rw [Fintype.sum_eq_single v (fun m3 hm3 => by
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply, if_neg (Ne.symm hm3)]; ring)]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply_eq]
    ring
  rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_comm]
  conv_rhs => rw [Fintype.sum_prod_type,
    Fintype.sum_eq_single r' (fun m1 hm1 => Finset.sum_eq_zero (fun m _ => by
      rw [Matrix.kroneckerMap_apply, Matrix.one_apply, if_neg hm1, zero_mul, mul_zero]))]
  refine Finset.sum_congr rfl (fun m2 _ => ?_)
  rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul, Matrix.of_apply, Finset.mul_sum]

theorem solution (d : ℕ) (hd : 0 < d) {κ : Type} [Fintype κ]
    (O : κ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    krausMap O ρ = ((d : ℂ) ^ 2) • WildeQIT.partialTraceRight
        (reindex (regroup d) (regroup d) (choiOp O) *
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρᵀ)) ∧
    krausMap O ρ = ((d : ℂ) ^ 4) • WildeQIT.partialTraceRight
        (reindex (Equiv.prodAssoc (Fin d × Fin d) (Fin d × Fin d) (Fin d × Fin d))
            (Equiv.prodAssoc (Fin d × Fin d) (Fin d × Fin d) (Fin d × Fin d))
            (reindex (regroup d) (regroup d) (choiOp O) ⊗ₖ
              (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) *
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
            (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρ) * projPhiPair d))) := by
  refine ⟨part8 d hd O ρ, ?_⟩
  rw [ptr_assoc]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h7 := eq7_thm d hd ρ
  have hX : WildeQIT.partialTraceRight
      (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρ) * projPhiPair d) =
      ((d : ℂ) ^ 2)⁻¹ • ρᵀ := by
    rw [← h7, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hd'), one_smul]
  rw [hX, Matrix.kronecker_smul, Matrix.mul_smul, ptr_smul, smul_smul, part8 d hd O ρ]
  congr 1
  field_simp
