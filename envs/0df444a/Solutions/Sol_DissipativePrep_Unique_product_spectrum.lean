-- Prove2me | solution 1 for DissipativePrep.Unique.product_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:36:09.209965+00:00
-- url     : https://prove2.me/submissions/0a843094-5ee6-4699-ac24-6a8001ec6535

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

lemma gksl_apply {d : ℕ} (D : LindbladData d) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    gkslGenerator D ρ = ∑ k, D.jump k * ρ * (D.jump k)ᴴ - driftK D * ρ - ρ * (driftK D)ᴴ := by
  simp [gkslGenerator, cpGenerator, sandwich, mul_assoc]

lemma lowerQ_cond {n : ℕ} (k : Fin n) (x z : Qubits n) :
    (z k = true ∧ x = Function.update z k false) ↔ (x k = false ∧ z = Function.update x k true) := by
  constructor
  · rintro ⟨h1, rfl⟩
    refine ⟨by simp, ?_⟩
    ext j
    by_cases hj : j = k
    · subst hj; simp [h1]
    · simp [hj]
  · rintro ⟨h1, rfl⟩
    refine ⟨by simp, ?_⟩
    ext j
    by_cases hj : j = k
    · subst hj; simp [h1]
    · simp [hj]

lemma lowerQ_apply' {n : ℕ} (k : Fin n) (x z : Qubits n) :
    lowerQ k x z = if (x k = false ∧ z = Function.update x k true) then 1 else 0 := by
  simp only [lowerQ, Matrix.of_apply]
  exact if_congr (lowerQ_cond k x z) rfl rfl

lemma lowerQ_mul_apply {n : ℕ} (k : Fin n) (T : Matrix (Qubits n) (Qubits n) ℂ) (x y : Qubits n) :
    (lowerQ k * T) x y = if x k = false then T (Function.update x k true) y else 0 := by
  rw [Matrix.mul_apply]
  simp only [lowerQ_apply', ite_and, ite_mul, one_mul, zero_mul]
  by_cases hx : x k = false
  · simp [hx]
  · simp [hx]

lemma star_ite_one (p : Prop) [Decidable p] : star (if p then (1 : ℂ) else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

lemma mul_lowerQ_conjT_apply {n : ℕ} (k : Fin n) (T : Matrix (Qubits n) (Qubits n) ℂ) (x y : Qubits n) :
    (T * (lowerQ k)ᴴ) x y = if y k = false then T x (Function.update y k true) else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, lowerQ_apply', ite_and, mul_ite, mul_one, mul_zero,
    star_ite_one]
  by_cases hy : y k = false
  · simp [hy]
  · simp [hy]

lemma lowerQ_cond' {n : ℕ} (k : Fin n) (x z : Qubits n) :
    (z k = false ∧ x = Function.update z k true) ↔ (x k = true ∧ z = Function.update x k false) := by
  constructor
  · rintro ⟨h1, rfl⟩
    refine ⟨by simp, ?_⟩
    ext j
    by_cases hj : j = k
    · subst hj; simp [h1]
    · simp [hj]
  · rintro ⟨h1, rfl⟩
    refine ⟨by simp, ?_⟩
    ext j
    by_cases hj : j = k
    · subst hj; simp [h1]
    · simp [hj]

lemma lowerQ_conjT_mul_self {n : ℕ} (k : Fin n) :
    (lowerQ k)ᴴ * lowerQ k = Matrix.diagonal (fun x : Qubits n => if x k = true then (1 : ℂ) else 0) := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, lowerQ_apply', lowerQ_cond', star_ite_one,
    Matrix.diagonal_apply]
  by_cases hx : x k = true
  · by_cases hy : y k = true
    · have hxy : Function.update x k false = Function.update y k false ↔ x = y := by
        constructor
        · intro h
          ext j
          by_cases hj : j = k
          · subst hj; simp [hx, hy]
          · simpa [Function.update_of_ne hj] using congrFun h j
        · rintro rfl; rfl
      simp only [hx, hy, true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_and]
      simp [hx, hy, hxy, eq_comm (a := Function.update y k false)]
    · have : ∀ z : Qubits n, (if y k = true ∧ z = Function.update y k false then (1:ℂ) else 0) = 0 := by
        intro z; simp [hy]
      simp [hx, hy, this]
      intro h; subst h; exact absurd hx hy
  · have : ∀ z : Qubits n, (if x k = true ∧ z = Function.update x k false then (1:ℂ) else 0) = 0 := by
      intro z; simp [hx]
    simp [hx, this]

lemma loc_id (g : ℝ) (p : Fin 4) (x y : Bool) :
    2 * (g : ℂ) * (if x = false ∧ y = false then localEigenoperator p true true else 0)
      - (g : ℂ) * (if x = true then 1 else 0) * localEigenoperator p x y
      - localEigenoperator p x y * ((g : ℂ) * (if y = true then 1 else 0))
    = localEigenvalue g p * localEigenoperator p x y := by
  fin_cases p <;> cases x <;> cases y <;> simp [localEigenoperator, localEigenvalue] <;> ring

def Gq {n : ℕ} (g : Fin n → ℝ) (T : Matrix (Qubits n) (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ k, ((2 * g k : ℝ) : ℂ) • (lowerQ k * T * (lowerQ k)ᴴ)
    - (∑ k, ((g k : ℝ) : ℂ) • ((lowerQ k)ᴴ * lowerQ k)) * T
    - T * (∑ k, ((g k : ℝ) : ℂ) • ((lowerQ k)ᴴ * lowerQ k))ᴴ

lemma diag_sum_eq {n : ℕ} (g : Fin n → ℝ) :
    (∑ k, ((g k : ℝ) : ℂ) • ((lowerQ k)ᴴ * lowerQ k)) =
      Matrix.diagonal (fun x : Qubits n => ∑ k, ((g k : ℝ) : ℂ) * (if x k = true then 1 else 0)) := by
  ext x y
  simp only [lowerQ_conjT_mul_self, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst h; simp
  · simp [h]

lemma Gq_apply {n : ℕ} (g : Fin n → ℝ) (T : Matrix (Qubits n) (Qubits n) ℂ) (x y : Qubits n) :
    Gq g T x y = (∑ k, 2 * (g k : ℂ) * (if x k = false ∧ y k = false then
        T (Function.update x k true) (Function.update y k true) else 0))
      - (∑ k, (g k : ℂ) * (if x k = true then 1 else 0)) * T x y
      - T x y * (∑ k, (g k : ℂ) * (if y k = true then 1 else 0)) := by
  unfold Gq
  rw [diag_sum_eq, Matrix.diagonal_conjTranspose]
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_assoc, lowerQ_mul_apply, mul_lowerQ_conjT_apply]
    by_cases h1 : x k = false <;> by_cases h2 : y k = false <;> simp [h1, h2]
  · simp only [mul_eq_mul_left_iff]
    left
    simp only [Pi.star_apply, star_sum, star_mul']
    exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

def Tq {n : ℕ} (i : Fin n → Fin 4) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y => ∏ k, localEigenoperator (i k) (x k) (y k)

lemma Gq_tensor {n : ℕ} (g : Fin n → ℝ) (i : Fin n → Fin 4) :
    Gq g (Tq i) = (∑ k, localEigenvalue (g k) (i k)) • Tq i := by
  ext x y
  rw [Gq_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hT : ∀ x y : Qubits n, Tq i x y = localEigenoperator (i k) (x k) (y k) *
      ∏ j ∈ Finset.univ.erase k, localEigenoperator (i j) (x j) (y j) := by
    intro x y
    simp only [Tq, Matrix.of_apply]
    rw [Finset.mul_prod_erase Finset.univ (fun j => localEigenoperator (i j) (x j) (y j)) (Finset.mem_univ k)]
  have hU : Tq i (Function.update x k true) (Function.update y k true) =
      localEigenoperator (i k) true true *
      ∏ j ∈ Finset.univ.erase k, localEigenoperator (i j) (x j) (y j) := by
    rw [hT]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ k := Finset.ne_of_mem_erase hj
    simp [Function.update_of_ne this]
  rw [hU, hT x y]
  have := loc_id (g k) (i k) (x k) (y k)
  set R := ∏ j ∈ Finset.univ.erase k, localEigenoperator (i j) (x j) (y j)
  calc _ = R * (2 * (g k : ℂ) * (if x k = false ∧ y k = false then localEigenoperator (i k) true true else 0)
      - (g k : ℂ) * (if x k = true then 1 else 0) * localEigenoperator (i k) (x k) (y k)
      - localEigenoperator (i k) (x k) (y k) * ((g k : ℂ) * (if y k = true then 1 else 0))) := by
        by_cases h1 : x k = false <;> by_cases h2 : y k = false <;> simp [h1, h2] <;> ring
    _ = _ := by rw [this]; ring

lemma sqrt_coef {g : ℝ} (hg : 0 < g) :
    ((Real.sqrt (2 * g) : ℝ) : ℂ) * star ((Real.sqrt (2 * g) : ℝ) : ℂ) = ((2 * g : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by linarith)]

lemma gksl_one_reindex {n : ℕ} (g : Fin n → ℝ) (hg : ∀ k, 0 < g k)
    (T : Matrix (Qubits n) (Qubits n) ℂ) :
    gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (Matrix.reindex (bitsEquivFin n) (bitsEquivFin n) T)
      = Matrix.reindex (bitsEquivFin n) (bitsEquivFin n) (Gq g T) := by
  set φ := Matrix.reindexAlgEquiv ℂ ℂ (bitsEquivFin n) with hφ
  have hφ' : ∀ M, Matrix.reindex (bitsEquivFin n) (bitsEquivFin n) M = φ M := fun M => rfl
  have hφc : ∀ M, φ Mᴴ = (φ M)ᴴ := fun M => by
    rw [← hφ', ← hφ']; exact (Matrix.conjTranspose_reindex _ _ _).symm
  rw [gksl_apply, hφ' T, hφ' (Gq g T)]
  have hdr : (prepData 1 g 0 Matrix.isHermitian_zero).drift = 0 := rfl
  have g2 : ∀ k : Fin n, (prepData 1 g 0 Matrix.isHermitian_zero).jump k =
      ((Real.sqrt (2 * g k) : ℝ) : ℂ) • φ (lowerQ k) := fun k => by
    show ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (1 * lower k * (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)ᴴ) = _
    rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul, ← hφ']
    rfl
  have s1 : ∀ τ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      ∑ k, (prepData 1 g 0 Matrix.isHermitian_zero).jump k * τ * ((prepData 1 g 0 Matrix.isHermitian_zero).jump k)ᴴ
      = ∑ k : Fin n, ((2 * g k : ℝ) : ℂ) • (φ (lowerQ k) * τ * (φ (lowerQ k))ᴴ) := fun τ =>
    Finset.sum_congr rfl fun (k : Fin n) _ => by
      rw [g2 k]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.conjTranspose_smul, smul_smul]
      rw [mul_comm, sqrt_coef (hg k)]
  have g4 : driftK (prepData 1 g 0 Matrix.isHermitian_zero) =
      ∑ k : Fin n, ((g k : ℝ) : ℂ) • ((φ (lowerQ k))ᴴ * φ (lowerQ k)) := by
    rw [driftK, hdr, smul_zero, zero_add, Finset.smul_sum]
    refine Finset.sum_congr rfl fun (k : Fin n) _ => ?_
    rw [g2 k, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
    congr 1
    have := sqrt_coef (hg k)
    rw [Complex.star_def] at this ⊢
    have h2 : ((g k : ℝ) : ℂ) = (1 / 2 : ℂ) * ((2 * g k : ℝ) : ℂ) := by push_cast; ring
    rw [h2, ← this]; ring
  rw [s1, g4]
  simp only [Gq, map_sub, map_sum, map_smul, map_mul, hφc, map_smul]

noncomputable def dualOp (q : Fin 4) (x y : Bool) : ℂ :=
  if q = 0 then (if x = y then 1 else 0)
  else if q = 1 then (if x ≠ y then 1 / 2 else 0)
  else if q = 2 then
    (if x = false ∧ y = true then Complex.I / 2
     else if x = true ∧ y = false then -(Complex.I / 2) else 0)
  else (if x = true ∧ y = true then -1 else 0)

lemma dual_pair (p q : Fin 4) :
    ∑ x : Bool, ∑ y : Bool, dualOp q x y * localEigenoperator p x y = if p = q then 1 else 0 := by
  fin_cases p <;> fin_cases q <;> simp [Fintype.sum_bool, dualOp, localEigenoperator] <;> ring_nf <;> simp

lemma prod_pair_sum {n : ℕ} (F : Fin n → Bool → Bool → ℂ) :
    ∑ x : Qubits n, ∑ y : Qubits n, ∏ k, F k (x k) (y k) = ∏ k, ∑ u : Bool, ∑ v : Bool, F k u v := by
  have h1 : ∀ k, ∑ u : Bool, ∑ v : Bool, F k u v = ∑ w : Bool × Bool, F k w.1 w.2 := fun k => by
    rw [Fintype.sum_prod_type]
  simp_rw [h1]
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Bool × Bool))) (fun k w => F k w.1 w.2),
    Fintype.piFinset_univ]
  calc ∑ x : Qubits n, ∑ y : Qubits n, ∏ k, F k (x k) (y k)
      = ∑ z : Qubits n × Qubits n, ∏ k, F k (z.1 k) (z.2 k) := (Fintype.sum_prod_type' _).symm
    _ = _ := (Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Bool) (fun _ => Bool))
        (fun z : Qubits n × Qubits n => ∏ k, F k (z.1 k) (z.2 k))).symm

noncomputable def dualFun {n : ℕ} (j : Fin n → Fin 4) : Matrix (Qubits n) (Qubits n) ℂ →ₗ[ℂ] ℂ where
  toFun M := ∑ x : Qubits n, ∑ y : Qubits n, (∏ k, dualOp (j k) (x k) (y k)) * M x y
  map_add' M N := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c M := by simp [Finset.mul_sum, mul_left_comm, Finset.smul_sum]

lemma dualFun_Tq {n : ℕ} (j i : Fin n → Fin 4) :
    dualFun j (Tq i) = if i = j then 1 else 0 := by
  simp only [dualFun, LinearMap.coe_mk, AddHom.coe_mk, Tq, Matrix.of_apply]
  have : ∀ x y : Qubits n, (∏ k, dualOp (j k) (x k) (y k)) * ∏ k, localEigenoperator (i k) (x k) (y k)
      = ∏ k, (dualOp (j k) (x k) (y k) * localEigenoperator (i k) (x k) (y k)) := fun x y => by
    rw [Finset.prod_mul_distrib]
  simp only [this]
  rw [prod_pair_sum (fun k u v => dualOp (j k) u v * localEigenoperator (i k) u v)]
  simp only [dual_pair]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

lemma Tq_linearIndependent {n : ℕ} : LinearIndependent ℂ (Tq (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have := congrArg (dualFun i) hc
  simp only [map_sum, map_smul, dualFun_Tq, map_zero] at this
  simpa using this

lemma conj_gen {d m : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1)
    (V : Fin m → Matrix (Fin d) (Fin d) ℂ) (σ : Matrix (Fin d) (Fin d) ℂ) :
    ∑ k, (U * V k * Uᴴ) * σ * (U * V k * Uᴴ)ᴴ
      - ((1 / 2 : ℂ) • ∑ k, (U * V k * Uᴴ)ᴴ * (U * V k * Uᴴ)) * σ
      - σ * ((1 / 2 : ℂ) • ∑ k, (U * V k * Uᴴ)ᴴ * (U * V k * Uᴴ))ᴴ
    = U * (∑ k, V k * (Uᴴ * σ * U) * (V k)ᴴ
      - ((1 / 2 : ℂ) • ∑ k, (V k)ᴴ * V k) * (Uᴴ * σ * U)
      - (Uᴴ * σ * U) * ((1 / 2 : ℂ) • ∑ k, (V k)ᴴ * V k)ᴴ) * Uᴴ := by
  have hK : ∀ k, (U * V k * Uᴴ)ᴴ * (U * V k * Uᴴ) = U * ((V k)ᴴ * V k) * Uᴴ := by
    intro k
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc U * ((V k)ᴴ * Uᴴ) * (U * V k * Uᴴ) = U * (V k)ᴴ * (Uᴴ * U) * V k * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp [Matrix.mul_assoc]
  set A : Matrix (Fin d) (Fin d) ℂ := (1 / 2 : ℂ) • ∑ k, (V k)ᴴ * V k with hA
  have hKU : (1 / 2 : ℂ) • ∑ k, (U * V k * Uᴴ)ᴴ * (U * V k * Uᴴ) = U * A * Uᴴ := by
    simp only [hK, hA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  have e1 : ∀ X, U * X * Uᴴ * σ = U * (X * (Uᴴ * σ * U)) * Uᴴ := fun X => by
    calc U * X * Uᴴ * σ = U * X * Uᴴ * σ * (U * Uᴴ) := by rw [h2, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e2 : ∀ X, σ * (U * X * Uᴴ) = U * ((Uᴴ * σ * U) * X) * Uᴴ := fun X => by
    calc σ * (U * X * Uᴴ) = (U * Uᴴ) * σ * (U * X * Uᴴ) := by rw [h2, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e3 : ∑ k, (U * V k * Uᴴ) * σ * (U * V k * Uᴴ)ᴴ
      = U * (∑ k, V k * (Uᴴ * σ * U) * (V k)ᴴ) * Uᴴ := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hAhh : (U * A * Uᴴ)ᴴ = U * Aᴴ * Uᴴ := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hKU, e3, e1, hAhh, e2]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

lemma gksl_prep_eq {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ)
    (σ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    gkslGenerator (prepData U g 0 Matrix.isHermitian_zero) σ =
      U * gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (Uᴴ * σ * U) * Uᴴ := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  rw [gksl_apply, gksl_apply]
  have key := conj_gen U h1 h2 (fun k : Fin n => ((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) σ
  have e0 : ∀ k : Fin n, ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (U * lower k * Uᴴ) =
      U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ := fun k => by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have e1 : ∀ k : Fin n, ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (1 * lower k * (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)ᴴ) =
      ((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k := fun k => by
    rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]
  have g1 : ∀ k : Fin n, (prepData U g 0 Matrix.isHermitian_zero).jump k =
      U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ := fun k => by
    show ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (U * lower k * Uᴴ) = _
    exact e0 k
  have g2 : ∀ k : Fin n, (prepData 1 g 0 Matrix.isHermitian_zero).jump k =
      ((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k := fun k => by
    show ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (1 * lower k * (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)ᴴ) = _
    exact e1 k
  have hdr : (prepData U g 0 Matrix.isHermitian_zero).drift = 0 := rfl
  have hdr1 : (prepData 1 g 0 Matrix.isHermitian_zero).drift = 0 := rfl
  have g3 : driftK (prepData U g 0 Matrix.isHermitian_zero) = (1 / 2 : ℂ) • ∑ k : Fin n,
      (U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ)ᴴ *
        (U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ) := by
    rw [driftK, hdr, smul_zero, zero_add]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [g1 k]
  have g4 : driftK (prepData 1 g 0 Matrix.isHermitian_zero) = (1 / 2 : ℂ) • ∑ k : Fin n,
      (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k)ᴴ * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) := by
    rw [driftK, hdr1, smul_zero, zero_add]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [g2 k]
  have s1 : ∀ τ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      ∑ k, (prepData U g 0 Matrix.isHermitian_zero).jump k * τ * ((prepData U g 0 Matrix.isHermitian_zero).jump k)ᴴ
      = ∑ k : Fin n, (U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ) * τ *
          (U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ)ᴴ := fun τ =>
    Finset.sum_congr rfl fun k _ => by rw [g1 k]
  have s2 : ∀ τ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      ∑ k, (prepData 1 g 0 Matrix.isHermitian_zero).jump k * τ * ((prepData 1 g 0 Matrix.isHermitian_zero).jump k)ᴴ
      = ∑ k : Fin n, (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * τ *
          (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k)ᴴ := fun τ =>
    Finset.sum_congr rfl fun k _ => by rw [g2 k]
  rw [s1, s2, g3, g4]
  exact key

lemma lev_cnt (g : ℝ) (p : Fin 4) :
    localEigenvalue g p = -((((![0, 1, 1, 2] : Fin 4 → Fin 3) p : Fin 3) : ℕ) : ℂ) * (g : ℂ) := by
  fin_cases p <;> simp [localEigenvalue]

lemma eig_tensor {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k)
    (i : Fin n → Fin 4) :
    gkslGenerator (prepData U g 0 Matrix.isHermitian_zero) (U * tensorEigenoperator i * Uᴴ) =
      (∑ k, localEigenvalue (g k) (i k)) • (U * tensorEigenoperator i * Uᴴ) := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  rw [gksl_prep_eq U hU g]
  have e : Uᴴ * (U * tensorEigenoperator i * Uᴴ) * U = tensorEigenoperator i := by
    calc Uᴴ * (U * tensorEigenoperator i * Uᴴ) * U = (Uᴴ * U) * tensorEigenoperator i * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  rw [e]
  have : gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (tensorEigenoperator i) =
      (∑ k, localEigenvalue (g k) (i k)) • tensorEigenoperator i := by
    have h := gksl_one_reindex g hg (Tq i)
    rw [Gq_tensor] at h
    exact h
  rw [this]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

end DissipativePrep.Unique

open DissipativePrep.Unique

theorem solution {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) :
    let G := gkslGenerator (prepData U g 0 Matrix.isHermitian_zero)
    let σ := fun i : Fin n → Fin 4 => U * tensorEigenoperator i * Uᴴ
    (∀ i, G (σ i) = (∑ k, localEigenvalue (g k) (i k)) • σ i) ∧
    LinearIndependent ℂ σ ∧
    Submodule.span ℂ (Set.range σ) = ⊤ ∧
    (∀ μ : ℂ, G.HasEigenvalue μ ↔
      ∃ m : Fin n → Fin 3, μ = -(∑ k, ((m k : ℕ) : ℂ) * (g k : ℂ))) := by
  intro G σ
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hEig : ∀ i, G (σ i) = (∑ k, localEigenvalue (g k) (i k)) • σ i := fun i => eig_tensor U hU g hg i
  -- linear independence
  have conj_inj : ∀ A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ, U * A * Uᴴ = U * B * Uᴴ → A = B := by
    intro A B h
    have key : ∀ A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ, A = Uᴴ * (U * A * Uᴴ) * U := fun A => by
      calc A = (Uᴴ * U) * A * (Uᴴ * U) := by rw [h1]; simp
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [key A, key B, h]
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (bitsEquivFin n)
  let f : Matrix (Qubits n) (Qubits n) ℂ →ₗ[ℂ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
    { toFun := fun X => U * φ X * Uᴴ
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hf : Function.Injective f := by
    intro X Y hXY
    exact φ.injective (conj_inj _ _ hXY)
  have hli : LinearIndependent ℂ σ := by
    have := Tq_linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)
    exact this
  have hspan : Submodule.span ℂ (Set.range σ) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_matrix, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      Module.finrank_self, mul_one, Fintype.card_fin, ← mul_pow]
    norm_num
  refine ⟨hEig, hli, hspan, fun μ => ?_⟩
  constructor
  · intro hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hvmem : v ∈ Submodule.span ℂ (Set.range σ) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hvmem
    have hGv : G v = μ • v := by
      have := hv.apply_eq_smul
      exact this
    have hzero : ∑ i, (c i * (∑ k, localEigenvalue (g k) (i k)) - μ * c i) • σ i = 0 := by
      have e1 : G v = ∑ i, (c i * (∑ k, localEigenvalue (g k) (i k))) • σ i := by
        rw [← hc, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hEig, smul_smul]
      have e2 : μ • v = ∑ i, (μ * c i) • σ i := by
        rw [← hc, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
      have e3 : ∑ i, (c i * (∑ k, localEigenvalue (g k) (i k))) • σ i = ∑ i, (μ * c i) • σ i := by
        rw [← e1, hGv, e2]
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [e3, sub_self]
    have hcz := Fintype.linearIndependent_iff.1 hli _ hzero
    have hne : ∃ i, c i ≠ 0 := by
      by_contra hall
      apply hv.2
      rw [← hc]
      have : ∀ i, c i = 0 := fun i => by
        by_contra h
        exact hall ⟨i, h⟩
      simp [this]
    obtain ⟨i, hi⟩ := hne
    have := hcz i
    have hμi : μ = ∑ k, localEigenvalue (g k) (i k) := by
      have h3 : c i * ((∑ k, localEigenvalue (g k) (i k)) - μ) = 0 := by linear_combination this
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hi
      · exact (sub_eq_zero.1 h).symm
    refine ⟨fun k => (![0, 1, 1, 2] : Fin 4 → Fin 3) (i k), ?_⟩
    rw [hμi]
    simp only [lev_cnt]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rintro ⟨m, rfl⟩
    have hsurj : ∀ q : Fin 3, ∃ p : Fin 4, (![0, 1, 1, 2] : Fin 4 → Fin 3) p = q := by
      intro q; fin_cases q
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
    choose p hp using hsurj
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := σ (fun k => p (m k))) ⟨?_, hli.ne_zero _⟩
    · rw [Module.End.mem_eigenspace_iff, hEig]
      congr 1
      simp only [lev_cnt, hp]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring

