-- Prove2me | solution 1 for ExactAmpDich.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T11:52:03.589209+00:00
-- url     : https://prove2.me/submissions/275c87dc-4eab-415e-b11f-11d17d82c4dd

import Definitions.Def_ExactAmpDich_QTract
import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates

set_option autoImplicit false
namespace ExactAmpDich
namespace TractProof
open QAlgorithms Matrix

 theorem tensorProd_mulVec {k : ℕ} (V : Fin k → Matrix Bool Bool ℂ)
    (ψ : Fin k → Bool → ℂ) (y : Qubits k) :
    (tensorProd V *ᵥ (fun x => ∏ i, ψ i (x i))) y =
      ∏ i, ∑ b : Bool, V i (y i) b * ψ i b := by
  classical
  unfold Matrix.mulVec dotProduct tensorProd
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin k) (b : Bool) => V i (y i) b * ψ i b)).symm

 theorem factorPerm_mulVec {k : ℕ} (σ : Equiv.Perm (Fin k))
    (v : Qubits k → ℂ) (y : Qubits k) :
    (factorPerm σ *ᵥ v) y = v (y ∘ σ.symm) := by
  classical
  unfold Matrix.mulVec dotProduct factorPerm
  have heq : ∀ x : Qubits k, y = x ∘ σ ↔ x = y ∘ σ.symm := by
    intro x
    constructor
    · intro h
      funext i
      have hi := congr_fun h (σ.symm i)
      simpa using hi.symm
    · rintro rfl
      ext i
      simp
  simp only [heq, ite_mul, one_mul, zero_mul]
  simp

 theorem factorPerm_product {k : ℕ} (σ : Equiv.Perm (Fin k))
    (ψ : Fin k → Bool → ℂ) (y : Qubits k) :
    (factorPerm σ *ᵥ (fun x => ∏ i, ψ i (x i))) y =
      ∏ i, ψ (σ i) (y i) := by
  rw [factorPerm_mulVec]
  exact (Equiv.prod_comp σ (fun i => ψ i (y (σ.symm i)))).symm.trans (by simp)

/-- Exact product-vector simulation for a tensor of one-qubit matrices followed by a wire
permutation. No normalization or division is used. -/
 theorem productPerm_mulVec {k : ℕ} (V : Fin k → Matrix Bool Bool ℂ)
    (σ : Equiv.Perm (Fin k)) (ψ : Fin k → Bool → ℂ) (y : Qubits k) :
    ((tensorProd V * factorPerm σ) *ᵥ (fun x => ∏ i, ψ i (x i))) y =
      ∏ i, ∑ b : Bool, V i (y i) b * ψ (σ i) b := by
  rw [← Matrix.mulVec_mulVec]
  have hf : (factorPerm σ *ᵥ (fun x => ∏ i, ψ i (x i))) =
      fun x => ∏ i, ψ (σ i) (x i) := by
    funext x
    exact factorPerm_product σ ψ x
  rw [hf]
  exact tensorProd_mulVec V (fun i => ψ (σ i)) y

 theorem tensorProd_mul {k : ℕ} (V W : Fin k → Matrix Bool Bool ℂ) :
    tensorProd V * tensorProd W = tensorProd (fun i => V i * W i) := by
  classical
  ext y x
  simp only [Matrix.mul_apply, tensorProd]
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin k) (b : Bool) => V i (y i) b * W i b (x i))).symm

 theorem tensorProd_one (k : ℕ) : tensorProd (fun _ : Fin k => (1 : Matrix Bool Bool ℂ)) = 1 := by
  classical
  ext y x
  by_cases h : y = x
  · subst x
    simp [tensorProd]
  · have hn : ∃ i, y i ≠ x i := Function.ne_iff.mp h
    obtain ⟨i, hi⟩ := hn
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Matrix.one_apply_ne hi

 theorem tensorProd_mulVec_injective {k : ℕ} (V : Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup Bool ℂ) :
    Function.Injective (fun v : Qubits k → ℂ => tensorProd V *ᵥ v) := by
  classical
  have hi : tensorProd (fun i => star (V i)) * tensorProd V = 1 := by
    rw [tensorProd_mul]
    have ht : (fun i => star (V i) * V i) = fun _ : Fin k => (1 : Matrix Bool Bool ℂ) := by
      funext i
      exact (hV i).1
    rw [ht, tensorProd_one]
  intro u v huv
  have hf := congrArg (fun z => tensorProd (fun i => star (V i)) *ᵥ z) huv
  simpa only [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec] using hf

 theorem factorPerm_mulVec_injective {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Function.Injective (fun v : Qubits k → ℂ => factorPerm σ *ᵥ v) := by
  intro u v h
  funext x
  have he := congr_fun h (x ∘ σ)
  simpa only [factorPerm_mulVec, Function.comp_def, Equiv.apply_symm_apply] using he

/-- The constructive direction of product-preserving structure: product unitaries followed
by tensor-factor permutations preserve every nonzero product vector. -/
 theorem productPerm_preservesProduct {k : ℕ} (V : Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup Bool ℂ) (σ : Equiv.Perm (Fin k)) :
    PreservesProduct (tensorProd V * factorPerm σ) := by
  classical
  rintro v ⟨hv, ψ, hψ⟩
  constructor
  · intro hz
    have hi := (tensorProd_mulVec_injective V hV).comp (factorPerm_mulVec_injective σ)
    apply hv
    apply hi
    simpa only [Function.comp_apply, Matrix.mulVec_mulVec, Matrix.mulVec_zero] using hz
  · refine ⟨fun i b => ∑ a : Bool, V i b a * ψ (σ i) a, ?_⟩
    intro y
    have he : v = fun x => ∏ i, ψ i (x i) := funext hψ
    rw [he]
    exact productPerm_mulVec V σ ψ y

end TractProof
end ExactAmpDich


set_option autoImplicit false

namespace ExactAmpDich.Hardness.Rigidity
open QAlgorithms Matrix
open scoped ComplexOrder

/-- Commutation with a diagonal matrix only couples indices in the same eigenvalue fiber.
Any coarser spectral observable has the same commutant inclusion. -/
lemma commute_diagonal_fiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ) (d e : ι → ℂ)
    (hde : ∀ i j, d i = d j → e i = e j)
    (hc : Commute C (Matrix.diagonal d)) : Commute C (Matrix.diagonal e) := by
  change C * Matrix.diagonal e = Matrix.diagonal e * C
  ext i j
  have hh := congrArg (fun M : Matrix ι ι ℂ => M i j) hc.eq
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hh ⊢
  by_cases hC : C i j = 0
  · simp [hC]
  · have hd : d i = d j := by
      apply (mul_left_cancel₀ hC)
      calc C i j * d i = d i * C i j := mul_comm _ _
           _ = C i j * d j := hh.symm
    rw [hde i j hd]
    exact mul_comm _ _

/-- Two positive eigenvalues admit an affine interpolation in their scalar logarithms. -/
lemma positive_bool_affine_log (lam : Bool → ℝ) (hlam : ∀ b, 0 < lam b) :
    ∃ A B : ℝ, ∀ b, lam b = A * Real.log (lam b) + B := by
  by_cases heq : lam false = lam true
  · refine ⟨0, lam false, ?_⟩
    intro b
    cases b <;> simp [heq]
  · have hl : Real.log (lam true) - Real.log (lam false) ≠ 0 := by
      intro hz
      apply heq
      exact (Real.log_injOn_pos (hlam false) (hlam true)) (sub_eq_zero.mp hz).symm
    refine ⟨(lam true - lam false) / (Real.log (lam true) - Real.log (lam false)),
      lam false - (lam true - lam false) / (Real.log (lam true) - Real.log (lam false)) * Real.log (lam false), ?_⟩
    intro b
    cases b
    · ring
    · field_simp [hl]
      ring

/-- Equality of tensor-product eigenvalues of a positive two-point spectrum implies equality
of the corresponding additive eigenvalues. This is the finite spectral content of tensor-log. -/
lemma positive_bool_product_refines_sum {k : ℕ} (lam : Bool → ℝ) (hlam : ∀ b, 0 < lam b)
    (x y : Qubits k) (hprod : (∏ i, lam (x i)) = ∏ i, lam (y i)) :
    (∑ i, lam (x i)) = ∑ i, lam (y i) := by
  obtain ⟨A, B, hAB⟩ := positive_bool_affine_log lam hlam
  have hl : (∑ i, Real.log (lam (x i))) = ∑ i, Real.log (lam (y i)) := by
    rw [← Real.log_prod (fun i _ => ne_of_gt (hlam (x i))),
      ← Real.log_prod (fun i _ => ne_of_gt (hlam (y i))), hprod]
  calc
    (∑ i, lam (x i)) = ∑ i, (A * Real.log (lam (x i)) + B) :=
      Finset.sum_congr rfl (fun i _ => hAB (x i))
    _ = ∑ i, (A * Real.log (lam (y i)) + B) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hl]
    _ = ∑ i, lam (y i) := Finset.sum_congr rfl (fun i _ => (hAB (y i)).symm)

lemma tensorProd_diagonal {k : ℕ} (d : Fin k → Bool → ℂ) :
    tensorProd (fun i => Matrix.diagonal (d i)) = Matrix.diagonal (fun x => ∏ i, d i (x i)) := by
  classical
  ext y x
  by_cases h : y = x
  · subst y
    simp [tensorProd]
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)

/-- Exact commutant inclusion for tensor and additive diagonal spectra. -/
lemma commute_positive_tensor_diagonal_implies_sum {k : ℕ}
    (C : Matrix (Qubits k) (Qubits k) ℂ) (lam : Bool → ℝ) (hlam : ∀ b, 0 < lam b)
    (hc : Commute C (tensorPow (Matrix.diagonal (fun b => (lam b : ℂ))) k)) :
    Commute C (Matrix.diagonal (fun x : Qubits k => (∑ i, (lam (x i) : ℂ)))) := by
  change Commute C (tensorProd (fun _ : Fin k => Matrix.diagonal (fun b => (lam b : ℂ)))) at hc
  rw [tensorProd_diagonal] at hc
  apply commute_diagonal_fiber C _ _ _ hc
  intro x y hxy
  have hprod : (∏ i, lam (x i)) = ∏ i, lam (y i) := by exact_mod_cast hxy
  exact_mod_cast positive_bool_product_refines_sum lam hlam x y hprod


noncomputable def localSum (A : Matrix Bool Bool ℂ) (k : ℕ) :
    Matrix (Qubits k) (Qubits k) ℂ :=
  ∑ i : Fin k, tensorProd (fun j => if j = i then A else 1)

lemma tensorPow_star (U : Matrix Bool Bool ℂ) (k : ℕ) :
    star (tensorPow U k) = tensorPow (star U) k := by
  ext y x
  simp only [tensorPow, tensorProd, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, star_prod]

lemma tensorPow_mul (U V : Matrix Bool Bool ℂ) (k : ℕ) :
    tensorPow U k * tensorPow V k = tensorPow (U * V) k :=
  TractProof.tensorProd_mul (fun _ => U) (fun _ => V)

lemma tensorPow_unitary (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (k : ℕ) :
    tensorPow U k ∈ Matrix.unitaryGroup (Qubits k) ℂ := by
  constructor
  · rw [tensorPow_star, tensorPow_mul, hU.1]
    exact TractProof.tensorProd_one k
  · rw [tensorPow_star, tensorPow_mul, hU.2]
    exact TractProof.tensorProd_one k

lemma tensorPow_conjugate (U A : Matrix Bool Bool ℂ) (k : ℕ) :
    tensorPow (U * A * star U) k = tensorPow U k * tensorPow A k * star (tensorPow U k) := by
  rw [tensorPow_star, tensorPow_mul, tensorPow_mul]

lemma localSum_conjugate (U A : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (k : ℕ) :
    tensorPow U k * localSum A k * star (tensorPow U k) = localSum (U * A * star U) k := by
  classical
  unfold localSum
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tensorPow_star]
  change tensorProd (fun _ : Fin k => U) * _ * tensorProd (fun _ : Fin k => star U) = _
  rw [TractProof.tensorProd_mul, TractProof.tensorProd_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · simp [hj]
  · simp [hj, hU.2]

lemma localSum_diagonal (d : Bool → ℂ) (k : ℕ) :
    localSum (Matrix.diagonal d) k = Matrix.diagonal (fun x : Qubits k => ∑ i, d (x i)) := by
  classical
  have hterm : ∀ i : Fin k,
      tensorProd (fun j => if j = i then Matrix.diagonal d else 1) =
        Matrix.diagonal (fun x : Qubits k => d (x i)) := by
    intro i
    have hf : (fun j : Fin k => if j = i then Matrix.diagonal d else 1) =
        fun j => Matrix.diagonal (fun b => if j = i then d b else 1) := by
      funext j
      by_cases hj : j = i
      · simp [hj]
      · simp [hj]
    rw [hf, tensorProd_diagonal]
    congr 1
    funext x
    simp
  unfold localSum
  simp_rw [hterm]
  ext y x
  by_cases h : y = x
  · subst y
    simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply, Matrix.diagonal_apply_ne _ h]


/-- The commutant step in Lemma 3.2. A positive two-level product metric determines its
additive local observable spectrally, so no tensor-log identity needs to be assumed. -/
theorem commute_tensorPow_implies_localSum (G : Matrix Bool Bool ℂ) (hG : G.PosDef)
    (k : ℕ) (C : Matrix (Qubits k) (Qubits k) ℂ) (hcomm : Commute C (tensorPow G k)) :
    Commute C (localSum G k) := by
  classical
  let U := hG.isHermitian.eigenvectorUnitary
  let lam : Bool → ℝ := hG.isHermitian.eigenvalues
  let D : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => (lam b : ℂ))
  let T : Matrix.unitaryGroup (Qubits k) ℂ :=
    ⟨tensorPow (U : Matrix Bool Bool ℂ) k, tensorPow_unitary _ U.property k⟩
  let F := Unitary.conjStarAlgAut ℂ _ T
  have hdecomp : G = (U : Matrix Bool Bool ℂ) * D * star (U : Matrix Bool Bool ℂ) :=
    hG.isHermitian.spectral_theorem
  have htensor : tensorPow G k = F (tensorPow D k) := by
    rw [hdecomp]
    change tensorPow ((U : Matrix Bool Bool ℂ) * D * star (U : Matrix Bool Bool ℂ)) k =
      tensorPow (U : Matrix Bool Bool ℂ) k * tensorPow D k * star (tensorPow (U : Matrix Bool Bool ℂ) k)
    exact tensorPow_conjugate _ _ _
  have hlocal : F (localSum D k) = localSum G k := by
    change tensorPow (U : Matrix Bool Bool ℂ) k * localSum D k *
      star (tensorPow (U : Matrix Bool Bool ℂ) k) = localSum G k
    rw [localSum_conjugate _ _ U.property, ← hdecomp]
  have hc : Commute (F.symm C) (tensorPow D k) := by
    rw [htensor] at hcomm
    have hh := hcomm.map F.symm.toMonoidHom
    change Commute (F.symm C) (F.symm (F (tensorPow D k))) at hh
    rw [F.symm_apply_apply] at hh
    exact hh
  have hd := commute_positive_tensor_diagonal_implies_sum (F.symm C) lam
    (hG.eigenvalues_pos) hc
  have hs : Commute (F.symm C) (localSum D k) := by
    simpa only [D, localSum_diagonal] using hd
  have hh := hs.map F.toMonoidHom
  change Commute (F (F.symm C)) (F (localSum D k)) at hh
  rw [F.apply_symm_apply, hlocal] at hh
  exact hh

end ExactAmpDich.Hardness.Rigidity

set_option autoImplicit false
namespace ExactAmpDich
namespace TractProof
namespace NormalizerFinite
open QAlgorithms QAlgorithms.Stabilizer Matrix

lemma I_pow_val_add (a b : ZMod 4) :
    Complex.I ^ a.val * Complex.I ^ b.val = Complex.I ^ (a + b).val := by
  rw [← pow_add, ZMod.val_add]
  conv_lhs => rw [← Nat.mod_add_div (a.val + b.val) 4]
  rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

lemma I_pow_sum {ι : Type*} (s : Finset ι) (k : ι → ZMod 4) :
    ∏ q ∈ s, Complex.I ^ (k q).val = Complex.I ^ (∑ q ∈ s, k q).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, I_pow_val_add]

lemma pauli_mul (P Q : Pauli) :
    P.mat * Q.mat = Complex.I ^ (Pauli.mul P Q).1.val • (Pauli.mul P Q).2.mat := by
  have h1 : ((1 : ZMod 4)).val = 1 := rfl
  have h3 : ((3 : ZMod 4)).val = 3 := rfl
  cases P <;> cases Q <;> ext a b <;> cases a <;> cases b <;>
    simp [Pauli.mul, Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.one_apply, h1, h3] <;> (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring_nf)

lemma tensorProd_smul {n : ℕ} (c : Fin n → ℂ) (a : Fin n → Matrix Bool Bool ℂ) :
    tensorProd (fun q => c q • a q) = (∏ q, c q) • tensorProd a := by
  ext y z
  simp [tensorProd, Finset.prod_mul_distrib]

lemma toMatrix_eq_tensor {n : ℕ} (P : PauliString n) :
    P.toMatrix = (Complex.I ^ P.phase.val) • tensorProd (fun q => (P.ops q).mat) := by
  ext y z
  simp [PauliString.toMatrix, tensorProd]

/-- Multiplicativity of the published symbolic Pauli product. The proof is the finite
entrywise calculation also used by the accepted Gottesman--Knill CHP correctness proof. -/
lemma toMatrix_mul {n : ℕ} (P Q : PauliString n) :
    (P.mul Q).toMatrix = P.toMatrix * Q.toMatrix := by
  rw [toMatrix_eq_tensor P, toMatrix_eq_tensor Q, toMatrix_eq_tensor (P.mul Q), Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, tensorProd_mul]
  have h : (fun q => (P.ops q).mat * (Q.ops q).mat) =
      fun q => Complex.I ^ (Pauli.mul (P.ops q) (Q.ops q)).1.val •
        (Pauli.mul (P.ops q) (Q.ops q)).2.mat := funext fun q => pauli_mul _ _
  rw [h, tensorProd_smul, smul_smul, I_pow_sum, I_pow_val_add, I_pow_val_add]
  rfl

lemma pauli_star (P : Pauli) : star P.mat = P.mat := by
  cases P <;> ext a b <;> cases a <;> cases b <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.one_apply]

lemma I_pow_val_neg (a : ZMod 4) : Complex.I ^ (-a).val = star (Complex.I ^ a.val) := by
  apply mul_left_cancel₀ (pow_ne_zero a.val Complex.I_ne_zero)
  rw [I_pow_val_add, add_neg_cancel]
  simp only [ZMod.val_zero, pow_zero, star_pow, Complex.star_def, Complex.conj_I]
  rw [← mul_pow]
  simp [mul_neg, Complex.I_sq]

lemma tensorProd_star {n : ℕ} (a : Fin n → Matrix Bool Bool ℂ) :
    star (tensorProd a) = tensorProd (fun q => star (a q)) := by
  ext y z
  simp only [tensorProd, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_prod]

/-- Symbolic adjoint; Pauli tensor factors are Hermitian. -/
def invPauli {n : ℕ} (P : PauliString n) : PauliString n := ⟨-P.phase, P.ops⟩

lemma toMatrix_inv {n : ℕ} (P : PauliString n) :
    (invPauli P).toMatrix = star P.toMatrix := by
  rw [toMatrix_eq_tensor, toMatrix_eq_tensor, star_smul, tensorProd_star]
  simp only [invPauli, I_pow_val_neg, pauli_star]

def onePauli (n : ℕ) : PauliString n := ⟨0, fun _ => .I⟩

lemma toMatrix_one (n : ℕ) : (onePauli n).toMatrix = 1 := by
  rw [toMatrix_eq_tensor]
  simp only [onePauli, ZMod.val_zero, pow_zero, one_smul, Pauli.mat, tensorProd_one]

lemma invPauli_mul {n : ℕ} (P : PauliString n) : (invPauli P).mul P = onePauli n := by
  have h : ∀ q, (Pauli.mul (P.ops q) (P.ops q)) = (0, .I) := by
    intro q
    cases P.ops q <;> rfl
  cases P
  simp only [invPauli, PauliString.mul, h, Finset.sum_const_zero, neg_add_cancel,
    add_zero, onePauli]

lemma toMatrix_unitary {n : ℕ} (P : PauliString n) :
    P.toMatrix ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  have h : star P.toMatrix * P.toMatrix = 1 := by
    rw [← toMatrix_inv, ← toMatrix_mul, invPauli_mul, toMatrix_one]
  exact ⟨h, mul_eq_one_comm.mp h⟩

noncomputable def pauliUnitary {n : ℕ} (P : PauliString n) :
    Matrix.unitaryGroup (Qubits n) ℂ := ⟨P.toMatrix, toMatrix_unitary P⟩

noncomputable def pauliSubgroup (n : ℕ) : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ) where
  carrier := {U | ∃ P : PauliString n, (U : Matrix (Qubits n) (Qubits n) ℂ) = P.toMatrix}
  one_mem' := ⟨onePauli n, (toMatrix_one n).symm⟩
  mul_mem' := by
    rintro U V ⟨P, hP⟩ ⟨Q, hQ⟩
    refine ⟨P.mul Q, ?_⟩
    change (U : Matrix (Qubits n) (Qubits n) ℂ) * (V : Matrix (Qubits n) (Qubits n) ℂ) = _
    rw [hP, hQ, ← toMatrix_mul]
  inv_mem' := by
    rintro U ⟨P, hP⟩
    refine ⟨invPauli P, ?_⟩
    change star (U : Matrix (Qubits n) (Qubits n) ℂ) = _
    rw [hP, ← toMatrix_inv]

/-- The closure in the public definition adds no matrices: the finite Pauli strings are
already closed under products and adjoints. -/
theorem pauliGroup_eq (n : ℕ) : pauliGroup n = pauliSubgroup n := by
  apply le_antisymm
  · exact (Subgroup.closure_le (pauliSubgroup n)).2 (fun _ h => h)
  · intro U hU
    exact Subgroup.subset_closure hU

instance pauliStringFintype (n : ℕ) : Fintype (PauliString n) := by
  let e : PauliString n ≃ ZMod 4 × (Fin n → Pauli) :=
    ⟨fun P => (P.phase, P.ops), fun p => ⟨p.1, p.2⟩, by intro P; cases P; rfl,
      by intro p; cases p; rfl⟩
  exact Fintype.ofEquiv _ e.symm

instance pauliSubgroupFinite (n : ℕ) : Finite (pauliSubgroup n) := by
  let f : PauliString n → pauliSubgroup n := fun P => ⟨pauliUnitary P, ⟨P, rfl⟩⟩
  apply Finite.of_surjective f
  rintro ⟨U, P, hP⟩
  refine ⟨P, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hP.symm

/-- Clifford normalizer membership is a finite conjunction of finite disjunctions of
quadratic matrix-entry equations. One-way containment suffices because the Pauli group is finite. -/
theorem normalizer_iff (n : ℕ) (U : Matrix.unitaryGroup (Qubits n) ℂ) :
    U ∈ Clifford.normalizer n ↔ ∀ P : PauliString n, ∃ Q : PauliString n,
      (U : Matrix (Qubits n) (Qubits n) ℂ) * P.toMatrix * star (U : Matrix (Qubits n) (Qubits n) ℂ) =
        Q.toMatrix := by
  classical
  constructor
  · intro hU P
    have hP : pauliUnitary P ∈ pauliGroup n := Subgroup.subset_closure ⟨P, rfl⟩
    have hQ := ((Subgroup.mem_normalizer_iff.mp hU) (pauliUnitary P)).mp hP
    rw [pauliGroup_eq n] at hQ
    obtain ⟨Q, hQ⟩ := hQ
    refine ⟨Q, ?_⟩
    exact hQ
  · intro h
    have hc : ∀ V ∈ pauliSubgroup n, U * V * U⁻¹ ∈ pauliSubgroup n := by
      rintro V ⟨P, hP⟩
      obtain ⟨Q, hQ⟩ := h P
      refine ⟨Q, ?_⟩
      change (U : Matrix (Qubits n) (Qubits n) ℂ) * (V : Matrix (Qubits n) (Qubits n) ℂ) *
        star (U : Matrix (Qubits n) (Qubits n) ℂ) = _
      rw [hP]
      exact hQ
    let f : pauliSubgroup n → pauliSubgroup n :=
      fun V => ⟨U * V * U⁻¹, hc V V.property⟩
    have hf : Function.Injective f := by
      intro V W he
      apply Subtype.ext
      have he' := congrArg Subtype.val he
      exact mul_left_cancel (mul_right_cancel he')
    have hs := Finite.surjective_of_injective hf
    change U ∈ Subgroup.normalizer (pauliGroup n : Set (Matrix.unitaryGroup (Qubits n) ℂ))
    rw [pauliGroup_eq n, Subgroup.mem_normalizer_iff]
    intro V
    constructor
    · exact hc V
    · intro hV
      obtain ⟨W, hW⟩ := hs ⟨U * V * U⁻¹, hV⟩
      have he' := congrArg Subtype.val hW
      have he : (W : Matrix.unitaryGroup (Qubits n) ℂ) = V :=
        mul_left_cancel (mul_right_cancel he')
      simpa only [he] using W.property

/-- Raw matrix form used by the rational first-order definition of `DC`. -/
theorem matrixClifford_iff (n : ℕ) (M : Matrix (Qubits n) (Qubits n) ℂ) :
    (∃ C : Matrix.unitaryGroup (Qubits n) ℂ,
      C ∈ Clifford.normalizer n ∧ (C : Matrix (Qubits n) (Qubits n) ℂ) = M) ↔
    M ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧ ∀ P : PauliString n, ∃ Q : PauliString n,
      M * P.toMatrix * star M = Q.toMatrix := by
  constructor
  · rintro ⟨C, hC, rfl⟩
    exact ⟨C.property, (normalizer_iff n C).mp hC⟩
  · rintro ⟨hM, h⟩
    exact ⟨⟨M, hM⟩, (normalizer_iff n ⟨M, hM⟩).mpr h, rfl⟩

end NormalizerFinite
end TractProof
end ExactAmpDich


set_option autoImplicit false

namespace ExactAmpDich.Hardness.Rigidity
open QAlgorithms QAlgorithms.Stabilizer Matrix
open scoped ComplexOrder

lemma trace_tensorProd {k : ℕ} (A : Fin k → Matrix Bool Bool ℂ) :
    Matrix.trace (tensorProd A) = ∏ i, Matrix.trace (A i) := by
  classical
  simp only [Matrix.trace]
  exact (Fintype.prod_sum (fun (i : Fin k) (b : Bool) => A i b b)).symm

lemma trace_pauli (P : Pauli) : Matrix.trace P.mat = if P = .I then 2 else 0 := by
  cases P <;> simp [Matrix.trace, Pauli.mat, pauliX, pauliY, pauliZ]

noncomputable def site {k : ℕ} (A : Matrix Bool Bool ℂ) (i : Fin k) :
    Matrix (Qubits k) (Qubits k) ℂ := tensorProd (fun j => if j = i then A else 1)

def localPauli {k : ℕ} (i : Fin k) (P : Pauli) : PauliString k :=
  ⟨0, fun j => if j = i then P else .I⟩

lemma localPauli_toMatrix {k : ℕ} (i : Fin k) (P : Pauli) :
    (localPauli i P).toMatrix = site P.mat i := by
  rw [TractProof.NormalizerFinite.toMatrix_eq_tensor]
  simp only [localPauli, ZMod.val_zero, pow_zero, one_smul, site]
  congr 1
  funext j
  split_ifs <;> rfl

lemma trace_pauliString {k : ℕ} (P : PauliString k) :
    Matrix.trace P.toMatrix =
      if ∀ i, P.ops i = .I then Complex.I ^ P.phase.val * 2 ^ k else 0 := by
  classical
  rw [TractProof.NormalizerFinite.toMatrix_eq_tensor, Matrix.trace_smul, trace_tensorProd]
  simp only [smul_eq_mul, trace_pauli]
  split_ifs with h
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), mul_zero]

lemma site_mul {k : ℕ} (A B : Matrix Bool Bool ℂ) (i : Fin k) :
    site A i * site B i = site (A * B) i := by
  classical
  rw [site, site, site, TractProof.tensorProd_mul]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj]

lemma trace_site {k : ℕ} (A : Matrix Bool Bool ℂ) (i : Fin k) :
    Matrix.trace (site A i) = Matrix.trace A * 2 ^ (k - 1) := by
  classical
  rw [site, trace_tensorProd]
  have hi : i ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ i
  rw [← Finset.mul_prod_erase (s := Finset.univ) (f := fun j =>
    Matrix.trace (if j = i then A else 1)) hi]
  simp only [if_true]
  have ht : ∀ j ∈ (Finset.univ : Finset (Fin k)).erase i,
      Matrix.trace (if j = i then A else 1) = (2 : ℂ) := by
    intro j hj
    simp only [if_neg (Finset.ne_of_mem_erase hj), Matrix.trace_one, Fintype.card_bool, Nat.cast_ofNat]
  simp_rw [Finset.prod_congr rfl ht]
  simp


lemma trace_site_mul_site_ne {k : ℕ} (A B : Matrix Bool Bool ℂ) (i j : Fin k)
    (hij : i ≠ j) (hA : Matrix.trace A = 0) : Matrix.trace (site A i * site B j) = 0 := by
  classical
  rw [site, site, TractProof.tensorProd_mul, trace_tensorProd]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hij, hA]

lemma trace_site_localSum {k : ℕ} (A G : Matrix Bool Bool ℂ) (i : Fin k)
    (hA : Matrix.trace A = 0) :
    Matrix.trace (site A i * localSum G k) = Matrix.trace (A * G) * 2 ^ (k - 1) := by
  classical
  rw [localSum, Finset.mul_sum, Matrix.trace_sum]
  rw [Finset.sum_eq_single i]
  · exact (congrArg Matrix.trace (site_mul A G i)).trans (trace_site (A * G) i)
  · intro j hj hji
    exact trace_site_mul_site_ne A G i j (Ne.symm hji) hA
  · simp

lemma trace_conjugate_mul_of_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A B : Matrix ι ι ℂ)
    (hB : Commute (U : Matrix ι ι ℂ) B) :
    Matrix.trace (((U : Matrix ι ι ℂ) * A * star (U : Matrix ι ι ℂ)) * B) = Matrix.trace (A * B) := by
  have hb : star (U : Matrix ι ι ℂ) * B * (U : Matrix ι ι ℂ) = B := by
    calc
      _ = star (U : Matrix ι ι ℂ) * (B * (U : Matrix ι ι ℂ)) := by rw [Matrix.mul_assoc]
      _ = star (U : Matrix ι ι ℂ) * ((U : Matrix ι ι ℂ) * B) := by rw [hB.eq]
      _ = B := by rw [← Matrix.mul_assoc, U.property.1, Matrix.one_mul]
  calc
    _ = Matrix.trace (A * (star (U : Matrix ι ι ℂ) * B * (U : Matrix ι ι ℂ))) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (U : Matrix ι ι ℂ)
        (A * (star (U : Matrix ι ι ℂ) * B))
    _ = _ := by rw [hb]

lemma trace_pauliString_mul_site_zero {k : ℕ} (P : PauliString k) (A : Matrix Bool Bool ℂ) (j : Fin k)
    (h : ∃ i, i ≠ j ∧ P.ops i ≠ .I) : Matrix.trace (P.toMatrix * site A j) = 0 := by
  classical
  obtain ⟨i, hij, hi⟩ := h
  rw [TractProof.NormalizerFinite.toMatrix_eq_tensor, Matrix.smul_mul, Matrix.trace_smul,
    site, TractProof.tensorProd_mul, trace_tensorProd]
  have hz : (∏ q : Fin k, Matrix.trace ((P.ops q).mat * (if q = j then A else 1))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hij, trace_pauli, hi]
  rw [hz, smul_zero]

lemma exists_nonidentity_away_of_weight_gt_one {k : ℕ} (P : PauliString k) (hP : 1 < P.weight)
    (j : Fin k) : ∃ i, i ≠ j ∧ P.ops i ≠ .I := by
  classical
  by_contra h
  have ho : ∀ i, P.ops i ≠ .I → i = j := by
    intro i hi
    by_contra hij
    exact h ⟨i, hij, hi⟩
  have hc : P.weight ≤ 1 := by
    change (Finset.univ.filter (fun i => P.ops i ≠ .I)).card ≤ 1
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact (ho a (Finset.mem_filter.mp ha).2).trans (ho b (Finset.mem_filter.mp hb).2).symm
  omega

lemma trace_high_weight_localSum_zero {k : ℕ} (P : PauliString k) (hP : 1 < P.weight)
    (G : Matrix Bool Bool ℂ) : Matrix.trace (P.toMatrix * localSum G k) = 0 := by
  classical
  rw [localSum, Finset.mul_sum, Matrix.trace_sum]
  exact Finset.sum_eq_zero (fun j _ =>
    trace_pauliString_mul_site_zero P G j (exists_nonidentity_away_of_weight_gt_one P hP j))

lemma pauli_weight_zero_iff {k : ℕ} (P : PauliString k) :
    P.weight = 0 ↔ ∀ i, P.ops i = .I := by
  classical
  simp [PauliString.weight, opsWeight, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

lemma weight_ne_zero_of_trace_zero {k : ℕ} (P : PauliString k) (hP : Matrix.trace P.toMatrix = 0) :
    P.weight ≠ 0 := by
  intro hw
  rw [trace_pauliString, if_pos ((pauli_weight_zero_iff P).mp hw)] at hP
  exact mul_ne_zero (pow_ne_zero P.phase.val Complex.I_ne_zero) (pow_ne_zero k (by norm_num)) hP

/-- A nonzero Bloch component forces every corresponding local Pauli to have a weight-one
Clifford image. The proof uses trace tensorization, not a Pauli-basis independence assumption. -/
theorem clifford_image_local_weight_one {k : ℕ} (G : Matrix Bool Bool ℂ) (hG : G.PosDef)
    (C : Matrix.unitaryGroup (Qubits k) ℂ) (hC : C ∈ Clifford.normalizer k)
    (hcomm : Commute (C : Matrix (Qubits k) (Qubits k) ℂ) (tensorPow G k))
    (P : Pauli) (hP : P ≠ .I) (hBloch : Matrix.trace (G * P.mat) ≠ 0) (i : Fin k) :
    ∃ Q : PauliString k, Q.weight = 1 ∧
      (C : Matrix (Qubits k) (Qubits k) ℂ) * site P.mat i *
        star (C : Matrix (Qubits k) (Qubits k) ℂ) = Q.toMatrix := by
  obtain ⟨Q, hQ⟩ := (TractProof.NormalizerFinite.normalizer_iff k C).mp hC (localPauli i P)
  rw [localPauli_toMatrix] at hQ
  have hlocal := commute_tensorPow_implies_localSum G hG k _ hcomm
  have hpTrace : Matrix.trace P.mat = 0 := by rw [trace_pauli, if_neg hP]
  have hnonzero : Matrix.trace (site P.mat i * localSum G k) ≠ 0 := by
    rw [trace_site_localSum P.mat G i hpTrace, Matrix.trace_mul_comm]
    exact mul_ne_zero hBloch (pow_ne_zero _ (by norm_num))
  have htrace : Matrix.trace Q.toMatrix = 0 := by
    rw [← hQ]
    have hh := trace_conjugate_mul_of_commute C (site P.mat i) 1 (Commute.one_right _)
    simp only [Matrix.mul_one] at hh
    rw [hh, trace_site, hpTrace, zero_mul]
  have hQnz := weight_ne_zero_of_trace_zero Q htrace
  have hQle : Q.weight ≤ 1 := by
    by_contra hn
    have hz := trace_high_weight_localSum_zero Q (by omega) G
    apply hnonzero
    rw [← hQ] at hz
    exact (trace_conjugate_mul_of_commute C (site P.mat i) (localSum G k) hlocal).symm.trans hz
  exact ⟨Q, by omega, hQ⟩

end ExactAmpDich.Hardness.Rigidity


set_option autoImplicit false

namespace ExactAmpDich.Hardness.Rigidity
open QAlgorithms QAlgorithms.Stabilizer Matrix
open scoped ComplexOrder

lemma site_apply {k : ℕ} (A : Matrix Bool Bool ℂ) (i : Fin k) (y x : Qubits k) :
    site A i y x = A (y i) (x i) * ∏ j ∈ (Finset.univ : Finset (Fin k)).erase i,
      (if y j = x j then (1 : ℂ) else 0) := by
  classical
  unfold site tensorProd
  rw [← Finset.mul_prod_erase (s := Finset.univ) (f := fun j => (if j = i then A else 1) (y j) (x j))
    (Finset.mem_univ i)]
  simp only [if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [Finset.ne_of_mem_erase hj, Matrix.one_apply]

lemma site_neg {k : ℕ} (A : Matrix Bool Bool ℂ) (i : Fin k) : site (-A) i = -site A i := by
  ext y x
  simp [site_apply]

lemma site_smul {k : ℕ} (c : ℂ) (A : Matrix Bool Bool ℂ) (i : Fin k) :
    site (c • A) i = c • site A i := by
  ext y x
  simp [site_apply, mul_assoc]

lemma site_commute_ne {k : ℕ} (A B : Matrix Bool Bool ℂ) (i j : Fin k) (hij : i ≠ j) :
    Commute (site A i) (site B j) := by
  change site A i * site B j = site B j * site A i
  rw [site, site, TractProof.tensorProd_mul, TractProof.tensorProd_mul]
  congr 1
  funext q
  by_cases hqi : q = i
  · subst q
    simp [hij]
  · by_cases hqj : q = j <;> simp [hqi, hqj, Ne.symm hij]

lemma pauli_anticommute (P Q : Pauli) (hP : P ≠ .I) (hQ : Q ≠ .I) (hPQ : P ≠ Q) :
    P.mat * Q.mat = -(Q.mat * P.mat) := by
  cases P <;> cases Q <;> simp_all
  all_goals ext a b; cases a <;> cases b <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply]

lemma site_pauli_anticommute {k : ℕ} (i : Fin k) (P Q : Pauli)
    (hP : P ≠ .I) (hQ : Q ≠ .I) (hPQ : P ≠ Q) :
    site P.mat i * site Q.mat i = -(site Q.mat i * site P.mat i) := by
  rw [site_mul, pauli_anticommute P Q hP hQ hPQ, site_neg, site_mul]

lemma unitary_anticommute_not_commute {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) (hB : B ∈ Matrix.unitaryGroup ι ℂ)
    (hab : A * B = -(B * A)) : ¬ Commute A B := by
  intro hc
  rw [← hc.eq] at hab
  have hz : A * B = 0 := by
    ext i j
    have hh := congrArg (fun M : Matrix ι ι ℂ => M i j) hab
    exact CharZero.eq_neg_self_iff.mp hh
  have hu := (Matrix.unitaryGroup ι ℂ).mul_mem hA hB
  have hh := hu.1
  rw [hz] at hh
  simp at hh

lemma weight_one_ops {k : ℕ} (P : PauliString k) (hP : P.weight = 1) :
    ∃ i : Fin k, P.ops i ≠ .I ∧ ∀ j, j ≠ i → P.ops j = .I := by
  classical
  have hc : (Finset.univ.filter (fun i => P.ops i ≠ .I)).card = 1 := hP
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  have hmem : i ∈ Finset.univ.filter (fun i => P.ops i ≠ .I) := by rw [hi]; simp
  refine ⟨i, (Finset.mem_filter.mp hmem).2, ?_⟩
  intro j hji
  by_contra hj
  have hm : j ∈ Finset.univ.filter (fun i => P.ops i ≠ .I) := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  rw [hi] at hm
  exact hji (Finset.mem_singleton.mp hm)

lemma weight_one_matrix {k : ℕ} (P : PauliString k) (hP : P.weight = 1) :
    ∃ i : Fin k, ∃ R : Pauli, R ≠ .I ∧
      P.toMatrix = Complex.I ^ P.phase.val • site R.mat i := by
  obtain ⟨i, hi, hall⟩ := weight_one_ops P hP
  refine ⟨i, P.ops i, hi, ?_⟩
  rw [TractProof.NormalizerFinite.toMatrix_eq_tensor]
  congr 1
  unfold site
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj, hall j hj, Pauli.mat]


lemma smul_commute (a b : ℂ) {k : ℕ} (A B : Matrix (Qubits k) (Qubits k) ℂ)
    (h : Commute A B) : Commute (a • A) (b • B) := by
  change (a • A) * (b • B) = (b • B) * (a • A)
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h.eq, mul_comm a b]

lemma conjugate_anticommute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix.unitaryGroup ι ℂ) (A B : Matrix ι ι ℂ) (h : A * B = -(B * A)) :
    ((C : Matrix ι ι ℂ) * A * star (C : Matrix ι ι ℂ)) *
        ((C : Matrix ι ι ℂ) * B * star (C : Matrix ι ι ℂ)) =
      -(((C : Matrix ι ι ℂ) * B * star (C : Matrix ι ι ℂ)) *
        ((C : Matrix ι ι ℂ) * A * star (C : Matrix ι ι ℂ))) := by
  let F := Unitary.conjStarAlgAut ℂ _ C
  have hh := congrArg F h
  change F A * F B = -(F B * F A)
  simpa only [map_mul, map_neg] using hh

lemma conjugate_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix.unitaryGroup ι ℂ) (A B : Matrix ι ι ℂ) (h : Commute A B) :
    Commute ((C : Matrix ι ι ℂ) * A * star (C : Matrix ι ι ℂ))
      ((C : Matrix ι ι ℂ) * B * star (C : Matrix ι ι ℂ)) := by
  let F := Unitary.conjStarAlgAut ℂ _ C
  have hh := h.map F.toMonoidHom
  change Commute (F A) (F B) at hh
  exact hh

lemma signed_site_anticommute_same {k : ℕ} (i j : Fin k) (P Q : Pauli) (a b : ℂ)
    (hA : a • site P.mat i ∈ Matrix.unitaryGroup (Qubits k) ℂ)
    (hB : b • site Q.mat j ∈ Matrix.unitaryGroup (Qubits k) ℂ)
    (hab : (a • site P.mat i) * (b • site Q.mat j) =
      -((b • site Q.mat j) * (a • site P.mat i))) : i = j ∧ P ≠ Q := by
  have hne := unitary_anticommute_not_commute _ _ hA hB hab
  have hij : i = j := by
    by_contra hij
    exact hne (smul_commute a b _ _ (site_commute_ne _ _ _ _ hij))
  refine ⟨hij, ?_⟩
  intro hPQ
  subst j
  subst Q
  exact hne (smul_commute a b _ _ (Commute.refl _))


structure LocalImagePair {k : ℕ} (C : Matrix (Qubits k) (Qubits k) ℂ)
    (P Q : Pauli) (i : Fin k) where
  target : Fin k
  first : Pauli
  second : Pauli
  first_ne_one : first ≠ .I
  second_ne_one : second ≠ .I
  axes_ne : first ≠ second
  a : ℂ
  b : ℂ
  a_norm_one : ‖a‖ = 1
  b_norm_one : ‖b‖ = 1
  a_ne_zero : a ≠ 0
  b_ne_zero : b ≠ 0
  first_image : C * site P.mat i * star C = a • site first.mat target
  second_image : C * site Q.mat i * star C = b • site second.mat target

/-- Anticommutation forces the two independent Bloch axes at one input site to land
on distinct Pauli axes at the same output site. -/
lemma exists_localImagePair {k : ℕ} (G : Matrix Bool Bool ℂ) (hG : G.PosDef)
    (C : Matrix.unitaryGroup (Qubits k) ℂ) (hC : C ∈ Clifford.normalizer k)
    (hcomm : Commute (C : Matrix (Qubits k) (Qubits k) ℂ) (tensorPow G k))
    (P Q : Pauli) (hP : P ≠ .I) (hQ : Q ≠ .I) (hPQ : P ≠ Q)
    (hBP : Matrix.trace (G * P.mat) ≠ 0) (hBQ : Matrix.trace (G * Q.mat) ≠ 0) (i : Fin k) :
    Nonempty (LocalImagePair (C : Matrix (Qubits k) (Qubits k) ℂ) P Q i) := by
  obtain ⟨A, hAweight, hA⟩ := clifford_image_local_weight_one G hG C hC hcomm P hP hBP i
  obtain ⟨B, hBweight, hB⟩ := clifford_image_local_weight_one G hG C hC hcomm Q hQ hBQ i
  obtain ⟨j, R, hR, hRmat⟩ := weight_one_matrix A hAweight
  obtain ⟨l, S, hS, hSmat⟩ := weight_one_matrix B hBweight
  have hAU := TractProof.NormalizerFinite.toMatrix_unitary A
  have hBU := TractProof.NormalizerFinite.toMatrix_unitary B
  rw [hRmat] at hAU
  rw [hSmat] at hBU
  have ha := conjugate_anticommute C (site P.mat i) (site Q.mat i)
    (site_pauli_anticommute i P Q hP hQ hPQ)
  rw [hA, hB, hRmat, hSmat] at ha
  obtain ⟨hjl, hRS⟩ := signed_site_anticommute_same j l R S _ _ hAU hBU ha
  subst l
  exact ⟨{
    target := j
    first := R
    second := S
    first_ne_one := hR
    second_ne_one := hS
    axes_ne := hRS
    a := Complex.I ^ A.phase.val
    b := Complex.I ^ B.phase.val
    a_norm_one := by simp
    b_norm_one := by simp
    a_ne_zero := pow_ne_zero _ Complex.I_ne_zero
    b_ne_zero := pow_ne_zero _ Complex.I_ne_zero
    first_image := hA.trans hRmat
    second_image := hB.trans hSmat }⟩


lemma site_pauli_unitary {k : ℕ} (P : Pauli) (i : Fin k) :
    site P.mat i ∈ Matrix.unitaryGroup (Qubits k) ℂ := by
  rw [← localPauli_toMatrix i P]
  exact TractProof.NormalizerFinite.toMatrix_unitary _

lemma unitary_matrix_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) : A ≠ 0 := by
  intro h
  have hh := hA.1
  rw [h] at hh
  simp at hh

lemma site_pauli_star {k : ℕ} (P : Pauli) (i : Fin k) : star (site P.mat i) = site P.mat i := by
  rw [site, TractProof.NormalizerFinite.tensorProd_star]
  congr 1
  funext j
  split_ifs <;> simp only [TractProof.NormalizerFinite.pauli_star, star_one]

lemma conjugate_pauli_star {k : ℕ} (C : Matrix.unitaryGroup (Qubits k) ℂ) (P : Pauli) (i : Fin k) :
    star ((C : Matrix (Qubits k) (Qubits k) ℂ) * site P.mat i * star (C : Matrix (Qubits k) (Qubits k) ℂ)) =
      (C : Matrix (Qubits k) (Qubits k) ℂ) * site P.mat i * star (C : Matrix (Qubits k) (Qubits k) ℂ) := by
  simp only [star_mul, star_star, site_pauli_star, Matrix.mul_assoc]

lemma real_unit_scalar_sign (a : ℂ) (ha : ‖a‖ = 1) (hreal : star a = a) : a = 1 ∨ a = -1 := by
  have him : a.im = 0 := by
    have h := congrArg Complex.im hreal
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have hn : a.re ^ 2 + a.im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, pow_two, ha, one_mul] using Complex.normSq_eq_norm_sq a
  have hre : a.re ^ 2 = 1 := by rw [him] at hn; nlinarith
  rcases sq_eq_one_iff.mp hre with h | h
  · left
    exact Complex.ext (by simpa using h) (by simpa using him)
  · right
    exact Complex.ext (by simpa using h) (by simpa using him)

lemma LocalImagePair.first_sign {k : ℕ} (C : Matrix.unitaryGroup (Qubits k) ℂ)
    (P Q : Pauli) (i : Fin k) (D : LocalImagePair (C : Matrix (Qubits k) (Qubits k) ℂ) P Q i) :
    D.a = 1 ∨ D.a = -1 := by
  apply real_unit_scalar_sign D.a D.a_norm_one
  apply smul_left_injective ℂ (unitary_matrix_ne_zero _ (site_pauli_unitary D.first D.target))
  have h := conjugate_pauli_star C P i
  rw [D.first_image, star_smul, site_pauli_star] at h
  exact h

lemma LocalImagePair.second_sign {k : ℕ} (C : Matrix.unitaryGroup (Qubits k) ℂ)
    (P Q : Pauli) (i : Fin k) (D : LocalImagePair (C : Matrix (Qubits k) (Qubits k) ℂ) P Q i) :
    D.b = 1 ∨ D.b = -1 := by
  apply real_unit_scalar_sign D.b D.b_norm_one
  apply smul_left_injective ℂ (unitary_matrix_ne_zero _ (site_pauli_unitary D.second D.target))
  have h := conjugate_pauli_star C Q i
  rw [D.second_image, star_smul, site_pauli_star] at h
  exact h

lemma smul_anticommute (a b : ℂ) {k : ℕ} (A B : Matrix (Qubits k) (Qubits k) ℂ)
    (h : A * B = -(B * A)) : (a • A) * (b • B) = -((b • B) * (a • A)) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h, smul_neg, mul_comm a b]

lemma unitary_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    ((C : Matrix ι ι ℂ) * A * star (C : Matrix ι ι ℂ)) ∈ Matrix.unitaryGroup ι ℂ := by
  exact (C * (⟨A, hA⟩ : Matrix.unitaryGroup ι ℂ) * C⁻¹).property

lemma localImagePair_target_injective {k : ℕ} (C : Matrix.unitaryGroup (Qubits k) ℂ)
    (P Q : Pauli) (D : ∀ i : Fin k, LocalImagePair (C : Matrix (Qubits k) (Qubits k) ℂ) P Q i) :
    Function.Injective (fun i => (D i).target) := by
  intro i j hij
  change (D i).target = (D j).target at hij
  by_contra hne
  have hab := conjugate_commute C (site P.mat i) (site P.mat j) (site_commute_ne _ _ _ _ hne)
  have hac := conjugate_commute C (site P.mat i) (site Q.mat j) (site_commute_ne _ _ _ _ hne)
  rw [(D i).first_image, (D j).first_image] at hab
  rw [(D i).first_image, (D j).second_image] at hac
  have hA := unitary_conjugate C _ (site_pauli_unitary P i)
  have hB := unitary_conjugate C _ (site_pauli_unitary P j)
  have hS := unitary_conjugate C _ (site_pauli_unitary Q j)
  rw [(D i).first_image, hij] at hA
  rw [(D j).first_image] at hB
  rw [(D j).second_image] at hS
  rw [hij] at hab hac
  by_cases hax : (D i).first = (D j).first
  · have hxs : (D i).first ≠ (D j).second := by
      intro h
      exact (D j).axes_ne (hax.symm.trans h)
    have ha := smul_anticommute (D i).a (D j).b _ _
      (site_pauli_anticommute (D j).target _ _ (D i).first_ne_one (D j).second_ne_one hxs)
    exact unitary_anticommute_not_commute _ _ hA hS ha hac
  · have ha := smul_anticommute (D i).a (D j).a _ _
      (site_pauli_anticommute (D j).target _ _ (D i).first_ne_one (D j).first_ne_one hax)
    exact unitary_anticommute_not_commute _ _ hA hB ha hab


lemma pauli_exhaustion_two (P Q R : Pauli) (hP : P ≠ .I) (hQ : Q ≠ .I) (hPQ : P ≠ Q) :
    R = .I ∨ R = P ∨ R = Q ∨ R = (Pauli.mul P Q).2 := by
  cases P <;> cases Q <;> cases R <;> simp_all [Pauli.mul]

lemma site_one {k : ℕ} (i : Fin k) : site (1 : Matrix Bool Bool ℂ) i = 1 := by
  simp only [site, ite_self]
  exact TractProof.tensorProd_one k

lemma commute_all_local_paulis_of_two {k : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (i : Fin k) (P Q : Pauli) (hP : P ≠ .I) (hQ : Q ≠ .I) (hPQ : P ≠ Q)
    (hcP : Commute M (site P.mat i)) (hcQ : Commute M (site Q.mat i)) :
    ∀ R : Pauli, Commute M (site R.mat i) := by
  intro R
  rcases pauli_exhaustion_two P Q R hP hQ hPQ with h | h | h | h
  · subst R
    change Commute M (site (1 : Matrix Bool Bool ℂ) i)
    rw [site_one]
    exact Commute.one_right M
  · subst R; exact hcP
  · subst R; exact hcQ
  · subst R
    have hh := hcP.mul_right hcQ
    have hpq : site P.mat i * site Q.mat i =
        Complex.I ^ (Pauli.mul P Q).1.val • site (Pauli.mul P Q).2.mat i := by
      rw [site_mul, TractProof.NormalizerFinite.pauli_mul, site_smul]
    rw [hpq] at hh
    change M * (Complex.I ^ (Pauli.mul P Q).1.val • site (Pauli.mul P Q).2.mat i) =
      (Complex.I ^ (Pauli.mul P Q).1.val • site (Pauli.mul P Q).2.mat i) * M at hh
    simp only [Matrix.mul_smul, Matrix.smul_mul] at hh
    exact (smul_right_inj (pow_ne_zero _ Complex.I_ne_zero)).mp hh


lemma exists_localImageEquiv {k : ℕ} (G : Matrix Bool Bool ℂ) (hG : G.PosDef)
    (C : Matrix.unitaryGroup (Qubits k) ℂ) (hC : C ∈ Clifford.normalizer k)
    (hcomm : Commute (C : Matrix (Qubits k) (Qubits k) ℂ) (tensorPow G k))
    (P Q : Pauli) (hP : P ≠ .I) (hQ : Q ≠ .I) (hPQ : P ≠ Q)
    (hBP : Matrix.trace (G * P.mat) ≠ 0) (hBQ : Matrix.trace (G * Q.mat) ≠ 0) :
    ∃ τ : Equiv.Perm (Fin k),
      ∃ D : ∀ i : Fin k, LocalImagePair (C : Matrix (Qubits k) (Qubits k) ℂ) P Q i,
        ∀ i, (D i).target = τ i := by
  classical
  let D := fun i => Classical.choice (exists_localImagePair G hG C hC hcomm P Q hP hQ hPQ hBP hBQ i)
  have hinj := localImagePair_target_injective C P Q D
  let τ := Equiv.ofBijective (fun i => (D i).target) ⟨hinj, Finite.surjective_of_injective hinj⟩
  exact ⟨τ, D, fun _ => rfl⟩

lemma nonzero_bloch_axes (G : Matrix Bool Bool ℂ)
    (hBloch : 2 ≤ (Finset.univ.filter fun P : Fin 3 =>
      (G * ![Pauli.X.mat, Pauli.Y.mat, Pauli.Z.mat] P).trace ≠ 0).card) :
    ∃ P Q : Pauli, P ≠ .I ∧ Q ≠ .I ∧ P ≠ Q ∧
      Matrix.trace (G * P.mat) ≠ 0 ∧ Matrix.trace (G * Q.mat) ≠ 0 := by
  classical
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.one_lt_card.mp (show 1 < _ from hBloch)
  let axis : Fin 3 → Pauli := ![.X, .Y, .Z]
  have hn : ∀ r : Fin 3, axis r ≠ .I := by intro r; fin_cases r <;> decide
  have hi : Function.Injective axis := by
    intro r s h
    fin_cases r <;> fin_cases s <;> simp_all [axis]
  refine ⟨axis r, axis s, hn r, hn s, fun h => hrs (hi h), ?_, ?_⟩
  · have h := (Finset.mem_filter.mp hr).2
    have he : (axis r).mat = ![Pauli.X.mat, Pauli.Y.mat, Pauli.Z.mat] r := by fin_cases r <;> rfl
    simpa only [he] using h
  · have h := (Finset.mem_filter.mp hs).2
    have he : (axis s).mat = ![Pauli.X.mat, Pauli.Y.mat, Pauli.Z.mat] s := by fin_cases s <;> rfl
    simpa only [he] using h

end ExactAmpDich.Hardness.Rigidity


set_option autoImplicit false

namespace ExactAmpDich.Hardness.Rigidity
open QAlgorithms QAlgorithms.Stabilizer Matrix

noncomputable def oneQubitEquiv : Bool ≃ Qubits 1 where
  toFun b := fun _ => b
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by
    funext i
    fin_cases i
    rfl

noncomputable def oneQubitMatrix (V : Matrix (Qubits 1) (Qubits 1) ℂ) : Matrix Bool Bool ℂ :=
  fun y x => V (fun _ => y) (fun _ => x)

lemma oneQubitMatrix_unitary (V : Matrix.unitaryGroup (Qubits 1) ℂ) :
    oneQubitMatrix (V : Matrix (Qubits 1) (Qubits 1) ℂ) ∈ Matrix.unitaryGroup Bool ℂ := by
  have hs : star ((V : Matrix (Qubits 1) (Qubits 1) ℂ).submatrix oneQubitEquiv oneQubitEquiv) =
      (star (V : Matrix (Qubits 1) (Qubits 1) ℂ)).submatrix oneQubitEquiv oneQubitEquiv := rfl
  change (V : Matrix (Qubits 1) (Qubits 1) ℂ).submatrix oneQubitEquiv oneQubitEquiv ∈ _
  constructor
  · rw [hs, Matrix.submatrix_mul_equiv, V.property.1, Matrix.submatrix_one_equiv]
  · rw [hs, Matrix.submatrix_mul_equiv, V.property.2, Matrix.submatrix_one_equiv]

lemma tensorProd_unitary {k : ℕ} (V : Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup Bool ℂ) :
    tensorProd V ∈ Matrix.unitaryGroup (Qubits k) ℂ := by
  constructor
  · rw [TractProof.NormalizerFinite.tensorProd_star, TractProof.tensorProd_mul]
    have hh : (fun i => star (V i) * V i) = fun _ : Fin k => (1 : Matrix Bool Bool ℂ) :=
      funext (fun i => (hV i).1)
    rw [hh, TractProof.tensorProd_one]
  · rw [TractProof.NormalizerFinite.tensorProd_star, TractProof.tensorProd_mul]
    have hh : (fun i => V i * star (V i)) = fun _ : Fin k => (1 : Matrix Bool Bool ℂ) :=
      funext (fun i => (hV i).2)
    rw [hh, TractProof.tensorProd_one]

noncomputable def permutationMatrix {ι : Type*} [DecidableEq ι] (e : Equiv.Perm ι) : Matrix ι ι ℂ :=
  fun y x => if y = e x then 1 else 0

lemma permutationMatrix_star {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Equiv.Perm ι) :
    star (permutationMatrix e) = permutationMatrix e.symm := by
  ext y x
  have he : x = e y ↔ y = e.symm x := by constructor <;> intro h <;> rw [h] <;> simp
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, permutationMatrix, he]
  split_ifs <;> simp

lemma permutationMatrix_mul_inv {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Equiv.Perm ι) :
    permutationMatrix e * permutationMatrix e.symm = 1 := by
  ext y x
  have he : ∀ z, y = e z ↔ z = e.symm y := by
    intro z
    constructor <;> intro h <;> rw [h] <;> simp
  simp [Matrix.mul_apply, permutationMatrix, he, Matrix.one_apply, eq_comm]

lemma permutationMatrix_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Equiv.Perm ι) :
    permutationMatrix e ∈ Matrix.unitaryGroup ι ℂ := by
  constructor
  · rw [permutationMatrix_star]
    exact permutationMatrix_mul_inv e.symm
  · rw [permutationMatrix_star]
    exact permutationMatrix_mul_inv e

noncomputable def wireEquiv {k : ℕ} (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Qubits k) where
  toFun x := x ∘ σ
  invFun x := x ∘ σ.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

lemma factorPerm_unitary {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    factorPerm σ ∈ Matrix.unitaryGroup (Qubits k) ℂ := permutationMatrix_unitary (wireEquiv σ)

lemma permutationMatrix_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) (A : Matrix ι ι ℂ) (y x : ι) :
    (permutationMatrix e * A * star (permutationMatrix e)) y x = A (e.symm y) (e.symm x) := by
  classical
  rw [permutationMatrix_star]
  have he : ∀ z, y = e z ↔ z = e.symm y := by
    intro z
    constructor <;> intro h <;> rw [h] <;> simp
  simp [Matrix.mul_apply, permutationMatrix, he]

lemma factorPerm_tensorProd_conjugate {k : ℕ} (σ : Equiv.Perm (Fin k))
    (V : Fin k → Matrix Bool Bool ℂ) :
    factorPerm σ * tensorProd V * star (factorPerm σ) = tensorProd (fun i => V (σ i)) := by
  classical
  ext y x
  have hh := permutationMatrix_conjugate (wireEquiv σ) (tensorProd V) y x
  change (factorPerm σ * tensorProd V * star (factorPerm σ)) y x = _ at hh
  rw [hh]
  change (∏ i : Fin k, V i (y (σ.symm i)) (x (σ.symm i))) = ∏ i : Fin k, V (σ i) (y i) (x i)
  exact (Equiv.prod_comp σ (fun i => V i (y (σ.symm i)) (x (σ.symm i)))).symm.trans (by simp)

lemma factorPerm_site_conjugate {k : ℕ} (σ : Equiv.Perm (Fin k)) (A : Matrix Bool Bool ℂ) (i : Fin k) :
    factorPerm σ * site A i * star (factorPerm σ) = site A (σ.symm i) := by
  rw [site, factorPerm_tensorProd_conjugate, site]
  congr 1
  funext j
  have he : σ j = i ↔ j = σ.symm i := by
    constructor
    · intro h; simpa using congrArg σ.symm h
    · intro h; rw [h]; simp
  by_cases hj : σ j = i
  · simp [hj, he.mp hj]
  · have hj' : j ≠ σ.symm i := fun h => hj (he.mpr h)
    simp [hj, hj']

lemma tensorProd_site_conjugate {k : ℕ} (V : Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup Bool ℂ) (A : Matrix Bool Bool ℂ) (i : Fin k) :
    tensorProd V * site A i * star (tensorProd V) = site (V i * A * star (V i)) i := by
  rw [TractProof.NormalizerFinite.tensorProd_star, site,
    TractProof.tensorProd_mul, TractProof.tensorProd_mul, site]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp [hj, (hV j).2]


lemma unit_scalar_mul_star (c : ℂ) (hc : ‖c‖ = 1) : c * star c = 1 := by
  change c * (starRingEnd ℂ c) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
  norm_num

lemma smul_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (hc : ‖c‖ = 1) (V : Matrix.unitaryGroup ι ℂ) :
    c • (V : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ := by
  have hcc := unit_scalar_mul_star c hc
  have hcc' : star c * c = 1 := by simpa only [mul_comm] using hcc
  constructor
  · simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, V.property.1, hcc, hcc', one_smul]
  · simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, V.property.2, hcc, hcc', one_smul]

noncomputable def phaseUnitary {n : ℕ} (c : ℂ) (hc : ‖c‖ = 1)
    (V : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix.unitaryGroup (Qubits n) ℂ :=
  ⟨c • (V : Matrix (Qubits n) (Qubits n) ℂ), smul_unitary c hc V⟩

lemma phaseUnitary_clifford {n : ℕ} (c : ℂ) (hc : ‖c‖ = 1)
    (V : Matrix.unitaryGroup (Qubits n) ℂ) (hV : V ∈ Clifford.normalizer n) :
    phaseUnitary c hc V ∈ Clifford.normalizer n := by
  apply (TractProof.NormalizerFinite.normalizer_iff n _).mpr
  intro P
  obtain ⟨Q, hQ⟩ := (TractProof.NormalizerFinite.normalizer_iff n V).mp hV P
  refine ⟨Q, ?_⟩
  change (c • (V : Matrix (Qubits n) (Qubits n) ℂ)) * P.toMatrix *
    star (c • (V : Matrix (Qubits n) (Qubits n) ℂ)) = Q.toMatrix
  simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (star c) c, unit_scalar_mul_star c hc, one_smul, hQ]

lemma oneQubitMatrix_phaseUnitary (c : ℂ) (hc : ‖c‖ = 1)
    (V : Matrix.unitaryGroup (Qubits 1) ℂ) :
    oneQubitMatrix (phaseUnitary c hc V : Matrix (Qubits 1) (Qubits 1) ℂ) =
      c • oneQubitMatrix (V : Matrix (Qubits 1) (Qubits 1) ℂ) := rfl

lemma tensorProd_phase_at {k : ℕ} (V : Fin k → Matrix Bool Bool ℂ) (c : ℂ) (i₀ : Fin k) :
    tensorProd (fun i => if i = i₀ then c • V i else V i) = c • tensorProd V := by
  classical
  have hf : (fun i => if i = i₀ then c • V i else V i) =
      fun i => (if i = i₀ then c else 1) • V i := by
    funext i
    by_cases hi : i = i₀ <;> simp [hi]
  rw [hf, TractProof.NormalizerFinite.tensorProd_smul]
  simp

noncomputable def absorbPhaseFamily {k : ℕ} (V : Fin k → Matrix.unitaryGroup (Qubits 1) ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) (i₀ : Fin k) : Fin k → Matrix.unitaryGroup (Qubits 1) ℂ :=
  fun i => if i = i₀ then phaseUnitary c hc (V i) else V i

lemma absorbPhaseFamily_clifford {k : ℕ} (V : Fin k → Matrix.unitaryGroup (Qubits 1) ℂ)
    (hV : ∀ i, V i ∈ Clifford.normalizer 1) (c : ℂ) (hc : ‖c‖ = 1) (i₀ : Fin k) :
    ∀ i, absorbPhaseFamily V c hc i₀ i ∈ Clifford.normalizer 1 := by
  intro i
  unfold absorbPhaseFamily
  split_ifs
  · exact phaseUnitary_clifford c hc (V i) (hV i)
  · exact hV i

lemma absorbPhaseFamily_tensor {k : ℕ} (V : Fin k → Matrix.unitaryGroup (Qubits 1) ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) (i₀ : Fin k) :
    tensorProd (fun i => oneQubitMatrix (absorbPhaseFamily V c hc i₀ i : Matrix (Qubits 1) (Qubits 1) ℂ)) =
      c • tensorProd (fun i => oneQubitMatrix (V i : Matrix (Qubits 1) (Qubits 1) ℂ)) := by
  classical
  have hf : (fun i => oneQubitMatrix (absorbPhaseFamily V c hc i₀ i : Matrix (Qubits 1) (Qubits 1) ℂ)) =
      fun i => if i = i₀ then c • oneQubitMatrix (V i : Matrix (Qubits 1) (Qubits 1) ℂ)
        else oneQubitMatrix (V i : Matrix (Qubits 1) (Qubits 1) ℂ) := by
    funext i
    by_cases hi : i = i₀ <;> simp only [absorbPhaseFamily, hi, if_true, if_false,
      oneQubitMatrix_phaseUnitary]
  rw [hf, tensorProd_phase_at]


lemma productPerm_site_conjugate {k : ℕ} (V : Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup Bool ℂ) (σ : Equiv.Perm (Fin k))
    (A : Matrix Bool Bool ℂ) (i : Fin k) :
    (tensorProd V * factorPerm σ) * site A i * star (tensorProd V * factorPerm σ) =
      site (V (σ.symm i) * A * star (V (σ.symm i))) (σ.symm i) := by
  rw [star_mul]
  calc
    _ = tensorProd V * (factorPerm σ * site A i * star (factorPerm σ)) * star (tensorProd V) := by
      noncomm_ring
    _ = _ := by rw [factorPerm_site_conjugate, tensorProd_site_conjugate V hV]

end ExactAmpDich.Hardness.Rigidity

set_option autoImplicit false
namespace ExactAmpDich
namespace TractProof
namespace PauliCommutant
open QAlgorithms QAlgorithms.Stabilizer Matrix NormalizerFinite

def zeroBits (n : ℕ) : Qubits n := fun _ => false

def zSign (b : Bool) : ℂ := if b then -1 else 1

def zPauli {n : ℕ} (i : Fin n) : PauliString n :=
  ⟨0, fun q => if q = i then .Z else .I⟩

lemma zPauli_matrix {n : ℕ} (i : Fin n) :
    (zPauli i).toMatrix = Matrix.diagonal (fun x => zSign (x i)) := by
  classical
  ext y x
  simp only [PauliString.toMatrix, zPauli, ZMod.val_zero, pow_zero, one_mul, Matrix.of_apply]
  by_cases h : y = x
  · subst x
    rw [Matrix.diagonal_apply_eq]
    rw [Finset.prod_eq_single i]
    · cases y i <;> simp [Pauli.mat, pauliZ, zSign]
    · intro q hq hqi
      simp [hqi, Pauli.mat]
    · simp
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    by_cases hqi : q = i
    · subst q
      cases hy : y i <;> cases hx : x i <;> simp_all [Pauli.mat, pauliZ]
    · simp [hqi, Pauli.mat, Matrix.one_apply_ne hq]

def xShift {n : ℕ} (mask x : Qubits n) : Qubits n := fun i => xor (x i) (mask i)

def xPauli {n : ℕ} (mask : Qubits n) : PauliString n :=
  ⟨0, fun q => if mask q then .X else .I⟩

@[simp] lemma xShift_self {n : ℕ} (x : Qubits n) : xShift x x = zeroBits n := by
  funext i
  cases hx : x i <;> simp [xShift, zeroBits, hx]

@[simp] lemma xShift_zero {n : ℕ} (x : Qubits n) : xShift x (zeroBits n) = x := by
  funext i
  cases hx : x i <;> simp [xShift, zeroBits, hx]

@[simp] lemma xShift_invol {n : ℕ} (mask x : Qubits n) : xShift mask (xShift mask x) = x := by
  funext i
  cases hx : x i <;> cases hm : mask i <;> simp [xShift, hx, hm]

lemma xPauli_matrix {n : ℕ} (mask : Qubits n) (y x : Qubits n) :
    (xPauli mask).toMatrix y x = if y = xShift mask x then 1 else 0 := by
  classical
  simp only [PauliString.toMatrix, xPauli, ZMod.val_zero, pow_zero, one_mul, Matrix.of_apply]
  have hv : ∀ q, (if mask q = true then Pauli.X else Pauli.I).mat (y q) (x q) =
      if y q = xShift mask x q then (1 : ℂ) else 0 := by
    intro q
    cases hm : mask q <;> cases hy : y q <;> cases hx : x q <;>
      simp [Pauli.mat, pauliX, xShift, Matrix.one_apply, hm, hy, hx]
  simp_rw [hv]
  by_cases h : y = xShift mask x
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro q hq
    simp [congr_fun h q]
  · rw [if_neg h]
    obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

lemma mul_xPauli {n : ℕ} (M : Matrix (Qubits n) (Qubits n) ℂ)
    (mask y x : Qubits n) : (M * (xPauli mask).toMatrix) y x = M y (xShift mask x) := by
  classical
  simp [Matrix.mul_apply, xPauli_matrix]

lemma xPauli_mul {n : ℕ} (M : Matrix (Qubits n) (Qubits n) ℂ)
    (mask y x : Qubits n) : ((xPauli mask).toMatrix * M) y x = M (xShift mask y) x := by
  classical
  have he : ∀ z : Qubits n, y = xShift mask z ↔ z = xShift mask y := by
    intro z
    constructor
    · intro h
      rw [h, xShift_invol]
    · rintro rfl
      rw [xShift_invol]
  simp [Matrix.mul_apply, xPauli_matrix, he]

/-- The full complex commutant of the actual Pauli matrices consists exactly of scalars. -/
theorem commutant_scalar {n : ℕ} (M : Matrix (Qubits n) (Qubits n) ℂ)
    (h : ∀ P : PauliString n, M * P.toMatrix = P.toMatrix * M) :
    M = M (zeroBits n) (zeroBits n) • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
  classical
  have hoff : ∀ y x : Qubits n, y ≠ x → M y x = 0 := by
    intro y x hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    have hz := congrFun (congrFun (h (zPauli i)) y) x
    rw [zPauli_matrix, Matrix.mul_diagonal, Matrix.diagonal_mul] at hz
    have hs : zSign (x i) - zSign (y i) ≠ 0 := by
      cases hx : x i <;> cases hy : y i <;> simp_all [zSign] <;> norm_num
    have hm : (zSign (x i) - zSign (y i)) * M y x = 0 := by
      linear_combination hz
    exact (mul_eq_zero.mp hm).resolve_left hs
  have hdiag : ∀ y : Qubits n, M y y = M (zeroBits n) (zeroBits n) := by
    intro y
    have hx := congrFun (congrFun (h (xPauli y)) y) (zeroBits n)
    simpa only [mul_xPauli, xPauli_mul, xShift_zero, xShift_self] using hx
  ext y x
  by_cases hyx : y = x
  · subst x
    simp [hdiag]
  · simp [hoff y x hyx, Matrix.one_apply_ne hyx]

/-- Equal Pauli conjugation actions determine a unitary up to one actual unit-modulus
scalar. No global phase is discarded from the resulting matrix equality. -/
theorem same_action_scalar {n : ℕ} (U V : Matrix.unitaryGroup (Qubits n) ℂ)
    (h : ∀ P : PauliString n,
      (U : Matrix (Qubits n) (Qubits n) ℂ) * P.toMatrix * star (U : Matrix (Qubits n) (Qubits n) ℂ) =
      (V : Matrix (Qubits n) (Qubits n) ℂ) * P.toMatrix * star (V : Matrix (Qubits n) (Qubits n) ℂ)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (U : Matrix (Qubits n) (Qubits n) ℂ) = c • (V : Matrix (Qubits n) (Qubits n) ℂ) := by
  let M := star (V : Matrix (Qubits n) (Qubits n) ℂ) * (U : Matrix (Qubits n) (Qubits n) ℂ)
  have hU : star (U : Matrix (Qubits n) (Qubits n) ℂ) * U = 1 := U.property.1
  have hV : star (V : Matrix (Qubits n) (Qubits n) ℂ) * V = 1 := V.property.1
  have hVr : (V : Matrix (Qubits n) (Qubits n) ℂ) * star (V : Matrix (Qubits n) (Qubits n) ℂ) = 1 := V.property.2
  have hc : ∀ P : PauliString n, M * P.toMatrix = P.toMatrix * M := by
    intro P
    have he := congrArg (fun A => star (V : Matrix (Qubits n) (Qubits n) ℂ) * A *
      (U : Matrix (Qubits n) (Qubits n) ℂ)) (h P)
    have hl : star (V : Matrix (Qubits n) (Qubits n) ℂ) *
        ((U : Matrix (Qubits n) (Qubits n) ℂ) * P.toMatrix * star (U : Matrix (Qubits n) (Qubits n) ℂ)) * U =
        M * P.toMatrix := by
      dsimp [M]
      simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
    have hr : star (V : Matrix (Qubits n) (Qubits n) ℂ) *
        ((V : Matrix (Qubits n) (Qubits n) ℂ) * P.toMatrix * star (V : Matrix (Qubits n) (Qubits n) ℂ)) * U =
        P.toMatrix * M := by
      dsimp [M]
      simp only [← Matrix.mul_assoc, hV, Matrix.one_mul]
    rw [hl, hr] at he
    exact he
  let c := M (zeroBits n) (zeroBits n)
  have hM : M = c • (1 : Matrix (Qubits n) (Qubits n) ℂ) := commutant_scalar M hc
  have hMM : star M * M = 1 := by
    dsimp [M]
    simp only [star_mul, star_star]
    calc
      _ = star (U : Matrix (Qubits n) (Qubits n) ℂ) *
          ((V : Matrix (Qubits n) (Qubits n) ℂ) * star (V : Matrix (Qubits n) (Qubits n) ℂ)) * U := by
        noncomm_ring
      _ = 1 := by rw [hVr, Matrix.mul_one, hU]
  rw [hM] at hMM
  have he := congrFun (congrFun hMM (zeroBits n)) (zeroBits n)
  have hcc : c * star c = 1 := by
    simpa only [star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one, one_mul] using he
  have hn : ‖c‖ * ‖c‖ = 1 := by
    simpa only [norm_mul, norm_star, norm_one] using congrArg norm hcc
  refine ⟨c, ?_, ?_⟩
  · nlinarith [norm_nonneg c]
  · calc
      (U : Matrix (Qubits n) (Qubits n) ℂ) = (V : Matrix (Qubits n) (Qubits n) ℂ) * M := by
        dsimp [M]
        rw [← Matrix.mul_assoc, hVr, Matrix.one_mul]
      _ = c • (V : Matrix (Qubits n) (Qubits n) ℂ) := by
        rw [hM, Matrix.mul_smul, Matrix.mul_one]

/-- For a fixed Pauli conjugation action, the homogeneous intertwining equations have
exactly one complex degree of freedom. The solution need not be invertible or unitary. -/
theorem intertwiner_scalar {n : ℕ} (U : Matrix.unitaryGroup (Qubits n) ℂ)
    (X : Matrix (Qubits n) (Qubits n) ℂ)
    (h : ∀ P : PauliString n, X * P.toMatrix =
      ((U : Matrix (Qubits n) (Qubits n) ℂ) * P.toMatrix * star (U : Matrix (Qubits n) (Qubits n) ℂ)) * X) :
    ∃ c : ℂ, X = c • (U : Matrix (Qubits n) (Qubits n) ℂ) := by
  let M := star (U : Matrix (Qubits n) (Qubits n) ℂ) * X
  have hU : star (U : Matrix (Qubits n) (Qubits n) ℂ) * U = 1 := U.property.1
  have hUr : (U : Matrix (Qubits n) (Qubits n) ℂ) * star (U : Matrix (Qubits n) (Qubits n) ℂ) = 1 := U.property.2
  have hc : ∀ P : PauliString n, M * P.toMatrix = P.toMatrix * M := by
    intro P
    dsimp [M]
    rw [Matrix.mul_assoc, h P]
    simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  let c := M (zeroBits n) (zeroBits n)
  have hM : M = c • (1 : Matrix (Qubits n) (Qubits n) ℂ) := commutant_scalar M hc
  refine ⟨c, ?_⟩
  calc
    X = (U : Matrix (Qubits n) (Qubits n) ℂ) * M := by
      dsimp [M]
      rw [← Matrix.mul_assoc, hUr, Matrix.one_mul]
    _ = c • (U : Matrix (Qubits n) (Qubits n) ℂ) := by
      rw [hM, Matrix.mul_smul, Matrix.mul_one]

end PauliCommutant
end TractProof
end ExactAmpDich

set_option autoImplicit false
namespace ExactAmpDich
namespace TractProof
namespace PauliCommutant
open QAlgorithms QAlgorithms.Stabilizer Matrix NormalizerFinite

def xSingle {n : ℕ} (i : Fin n) : PauliString n := ⟨0, fun q => if q = i then .X else .I⟩

noncomputable def xSet {n : ℕ} (s : Finset (Fin n)) : PauliString n :=
  ⟨0, fun q => if q ∈ s then .X else .I⟩

lemma xSet_empty (n : ℕ) : (xSet (∅ : Finset (Fin n))).toMatrix = 1 := by
  have he : xSet (∅ : Finset (Fin n)) = onePauli n := by
    simp [xSet, onePauli]
  rw [he, toMatrix_one]

lemma xSet_insert {n : ℕ} (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s) :
    xSet (insert i s) = (xSingle i).mul (xSet s) := by
  classical
  have hm : ∀ q, Pauli.mul (if q = i then .X else .I) (if q ∈ s then .X else .I) =
      (0, if q ∈ insert i s then .X else .I) := by
    intro q
    by_cases hqi : q = i
    · subst q
      simp [hi, Pauli.mul]
    · by_cases hq : q ∈ s <;> simp [hqi, hq, Pauli.mul]
  unfold xSet xSingle PauliString.mul
  congr 1
  · simp only [hm, Finset.sum_const_zero, zero_add]
  · funext q
    simp only [hm]

lemma commute_xSet {n : ℕ} (M : Matrix (Qubits n) (Qubits n) ℂ)
    (hX : ∀ i : Fin n, M * (xSingle i).toMatrix = (xSingle i).toMatrix * M)
    (s : Finset (Fin n)) : M * (xSet s).toMatrix = (xSet s).toMatrix * M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [xSet_empty]
  | insert i s hi ih =>
    rw [xSet_insert s i hi, toMatrix_mul]
    calc
      _ = (M * (xSingle i).toMatrix) * (xSet s).toMatrix := by simp only [Matrix.mul_assoc]
      _ = ((xSingle i).toMatrix * M) * (xSet s).toMatrix := by rw [hX]
      _ = (xSingle i).toMatrix * ((xSet s).toMatrix * M) := by rw [Matrix.mul_assoc, ih]
      _ = _ := by simp only [Matrix.mul_assoc]

lemma commute_xPauli {n : ℕ} (M : Matrix (Qubits n) (Qubits n) ℂ)
    (hX : ∀ i : Fin n, M * (xSingle i).toMatrix = (xSingle i).toMatrix * M)
    (mask : Qubits n) : M * (xPauli mask).toMatrix = (xPauli mask).toMatrix * M := by
  classical
  have he : xPauli mask = xSet (Finset.univ.filter (fun i => mask i = true)) := by
    unfold xPauli xSet
    congr 1
    funext q
    simp
  rw [he]
  exact commute_xSet M hX _

/-- Single-site X and Z operators already determine the scalar commutant. -/
theorem commutant_scalar_of_single_XZ {n : ℕ} (M : Matrix (Qubits n) (Qubits n) ℂ)
    (hX : ∀ i : Fin n, M * (xSingle i).toMatrix = (xSingle i).toMatrix * M)
    (hZ : ∀ i : Fin n, M * (zPauli i).toMatrix = (zPauli i).toMatrix * M) :
    M = M (zeroBits n) (zeroBits n) • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
  classical
  have hoff : ∀ y x : Qubits n, y ≠ x → M y x = 0 := by
    intro y x hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    have hz := congrFun (congrFun (hZ i) y) x
    rw [zPauli_matrix, Matrix.mul_diagonal, Matrix.diagonal_mul] at hz
    have hs : zSign (x i) - zSign (y i) ≠ 0 := by
      cases hx : x i <;> cases hy : y i <;> simp_all [zSign] <;> norm_num
    have hm : (zSign (x i) - zSign (y i)) * M y x = 0 := by linear_combination hz
    exact (mul_eq_zero.mp hm).resolve_left hs
  have hdiag : ∀ y : Qubits n, M y y = M (zeroBits n) (zeroBits n) := by
    intro y
    have hx := congrFun (congrFun (commute_xPauli M hX y) y) (zeroBits n)
    simpa only [mul_xPauli, xPauli_mul, xShift_zero, xShift_self] using hx
  ext y x
  by_cases hyx : y = x
  · subst x
    simp [hdiag]
  · simp [hoff y x hyx, Matrix.one_apply_ne hyx]

end PauliCommutant
end TractProof
end ExactAmpDich


set_option autoImplicit false

namespace ExactAmpDich.Hardness.Rigidity
open QAlgorithms QAlgorithms.Stabilizer Matrix TractProof.PauliCommutant

/-- Any two distinct nonidentity local Pauli axes determine the scalar commutant. -/
lemma commutant_scalar_of_two_axes {k : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (P Q : Pauli) (hP : P ≠ .I) (hQ : Q ≠ .I) (hPQ : P ≠ Q)
    (hcP : ∀ i, Commute M (site P.mat i)) (hcQ : ∀ i, Commute M (site Q.mat i)) :
    M = M (zeroBits k) (zeroBits k) • (1 : Matrix (Qubits k) (Qubits k) ℂ) := by
  apply commutant_scalar_of_single_XZ
  · intro i
    change M * (localPauli i .X).toMatrix = (localPauli i .X).toMatrix * M
    rw [localPauli_toMatrix]
    exact (commute_all_local_paulis_of_two M i P Q hP hQ hPQ (hcP i) (hcQ i) .X).eq
  · intro i
    change M * (localPauli i .Z).toMatrix = (localPauli i .Z).toMatrix * M
    rw [localPauli_toMatrix]
    exact (commute_all_local_paulis_of_two M i P Q hP hQ hPQ (hcP i) (hcQ i) .Z).eq

lemma same_conjugate_imp_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ)
    (h : (U : Matrix ι ι ℂ) * A * star (U : Matrix ι ι ℂ) =
      (V : Matrix ι ι ℂ) * A * star (V : Matrix ι ι ℂ)) :
    Commute (star (V : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)) A := by
  have he := congrArg (fun X : Matrix ι ι ℂ => star (V : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ)) h
  have hl : star (V : Matrix ι ι ℂ) * ((U : Matrix ι ι ℂ) * A * star (U : Matrix ι ι ℂ)) * U =
      (star (V : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)) * A := by
    simp only [Matrix.mul_assoc, U.property.1, Matrix.mul_one]
  have hr : star (V : Matrix ι ι ℂ) * ((V : Matrix ι ι ℂ) * A * star (V : Matrix ι ι ℂ)) * U =
      A * (star (V : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)) := by
    simp only [← Matrix.mul_assoc, V.property.1, Matrix.one_mul]
  rw [hl, hr] at he
  exact he

/-- Matching two Pauli axes per site determines the exact unitary up to a single global phase. -/
theorem same_two_axis_action_scalar {k : ℕ} (U V : Matrix.unitaryGroup (Qubits k) ℂ)
    (P Q : Pauli) (hP : P ≠ .I) (hQ : Q ≠ .I) (hPQ : P ≠ Q)
    (hcP : ∀ i, (U : Matrix (Qubits k) (Qubits k) ℂ) * site P.mat i * star (U : Matrix (Qubits k) (Qubits k) ℂ) =
      (V : Matrix (Qubits k) (Qubits k) ℂ) * site P.mat i * star (V : Matrix (Qubits k) (Qubits k) ℂ))
    (hcQ : ∀ i, (U : Matrix (Qubits k) (Qubits k) ℂ) * site Q.mat i * star (U : Matrix (Qubits k) (Qubits k) ℂ) =
      (V : Matrix (Qubits k) (Qubits k) ℂ) * site Q.mat i * star (V : Matrix (Qubits k) (Qubits k) ℂ)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (U : Matrix (Qubits k) (Qubits k) ℂ) = c • (V : Matrix (Qubits k) (Qubits k) ℂ) := by
  let M := star (V : Matrix (Qubits k) (Qubits k) ℂ) * (U : Matrix (Qubits k) (Qubits k) ℂ)
  let c := M (zeroBits k) (zeroBits k)
  have hM : M = c • (1 : Matrix (Qubits k) (Qubits k) ℂ) :=
    commutant_scalar_of_two_axes M P Q hP hQ hPQ
      (fun i => same_conjugate_imp_commute U V _ (hcP i))
      (fun i => same_conjugate_imp_commute U V _ (hcQ i))
  have hMM : star M * M = 1 := by
    dsimp [M]
    simp only [star_mul, star_star]
    calc
      _ = star (U : Matrix (Qubits k) (Qubits k) ℂ) *
          ((V : Matrix (Qubits k) (Qubits k) ℂ) * star (V : Matrix (Qubits k) (Qubits k) ℂ)) * U := by noncomm_ring
      _ = 1 := by rw [V.property.2, Matrix.mul_one, U.property.1]
  rw [hM] at hMM
  have he := congrFun (congrFun hMM (zeroBits k)) (zeroBits k)
  have hcc : c * star c = 1 := by
    simpa only [star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one, one_mul] using he
  have hn : ‖c‖ * ‖c‖ = 1 := by
    simpa only [norm_mul, norm_star, norm_one] using congrArg norm hcc
  refine ⟨c, by nlinarith [norm_nonneg c], ?_⟩
  calc
    (U : Matrix (Qubits k) (Qubits k) ℂ) = (V : Matrix (Qubits k) (Qubits k) ℂ) * M := by
      dsimp [M]
      rw [← Matrix.mul_assoc, V.property.2, Matrix.one_mul]
    _ = c • (V : Matrix (Qubits k) (Qubits k) ℂ) := by rw [hM, Matrix.mul_smul, Matrix.mul_one]

end ExactAmpDich.Hardness.Rigidity


set_option autoImplicit false

namespace ExactAmpDich.Hardness.Rigidity
open QAlgorithms QAlgorithms.Stabilizer Matrix

/-- Exact tensor/wire assembly from the local Clifford representatives. Any remaining
unit-modulus global scalar is absorbed into one local Clifford factor. -/
theorem assemble_local_cliffords {k : ℕ} (hk : 1 ≤ k)
    (C : Matrix.unitaryGroup (Qubits k) ℂ) (P Q : Pauli)
    (hP : P ≠ .I) (hQ : Q ≠ .I) (hPQ : P ≠ Q)
    (τ : Equiv.Perm (Fin k))
    (D : ∀ i, LocalImagePair (C : Matrix (Qubits k) (Qubits k) ℂ) P Q i)
    (hτ : ∀ i, (D i).target = τ i)
    (V : Fin k → Matrix.unitaryGroup (Qubits 1) ℂ)
    (hV : ∀ i, V i ∈ Clifford.normalizer 1)
    (hVP : ∀ i,
      oneQubitMatrix (V i : Matrix (Qubits 1) (Qubits 1) ℂ) * P.mat *
        star (oneQubitMatrix (V i : Matrix (Qubits 1) (Qubits 1) ℂ)) = (D i).a • (D i).first.mat)
    (hVQ : ∀ i,
      oneQubitMatrix (V i : Matrix (Qubits 1) (Qubits 1) ℂ) * Q.mat *
        star (oneQubitMatrix (V i : Matrix (Qubits 1) (Qubits 1) ℂ)) = (D i).b • (D i).second.mat) :
    ∃ (W : Fin k → Matrix.unitaryGroup (Qubits 1) ℂ) (σ : Equiv.Perm (Fin k)),
      (∀ i, W i ∈ Clifford.normalizer 1) ∧
      (C : Matrix (Qubits k) (Qubits k) ℂ) =
        tensorProd (fun i => oneQubitMatrix (W i : Matrix (Qubits 1) (Qubits 1) ℂ)) * factorPerm σ := by
  let B : Fin k → Matrix.unitaryGroup (Qubits 1) ℂ := fun j => V (τ.symm j)
  let N : Fin k → Matrix Bool Bool ℂ := fun j => oneQubitMatrix (B j : Matrix (Qubits 1) (Qubits 1) ℂ)
  have hN : ∀ j, N j ∈ Matrix.unitaryGroup Bool ℂ := fun j => oneQubitMatrix_unitary (B j)
  let U : Matrix.unitaryGroup (Qubits k) ℂ :=
    ⟨tensorProd N * factorPerm τ.symm,
      (Matrix.unitaryGroup (Qubits k) ℂ).mul_mem (tensorProd_unitary N hN) (factorPerm_unitary τ.symm)⟩
  have hact : ∀ (A : Matrix Bool Bool ℂ) (i : Fin k),
      (U : Matrix (Qubits k) (Qubits k) ℂ) * site A i * star (U : Matrix (Qubits k) (Qubits k) ℂ) =
        site (oneQubitMatrix (V i : Matrix (Qubits 1) (Qubits 1) ℂ) * A *
          star (oneQubitMatrix (V i : Matrix (Qubits 1) (Qubits 1) ℂ))) (τ i) := by
    intro A i
    simpa only [U, Equiv.symm_symm, N, B, Equiv.symm_apply_apply] using
      productPerm_site_conjugate N hN τ.symm A i
  have hCP : ∀ i,
      (C : Matrix (Qubits k) (Qubits k) ℂ) * site P.mat i * star (C : Matrix (Qubits k) (Qubits k) ℂ) =
        (U : Matrix (Qubits k) (Qubits k) ℂ) * site P.mat i * star (U : Matrix (Qubits k) (Qubits k) ℂ) := by
    intro i
    rw [(D i).first_image, hτ i, hact, hVP i, site_smul]
  have hCQ : ∀ i,
      (C : Matrix (Qubits k) (Qubits k) ℂ) * site Q.mat i * star (C : Matrix (Qubits k) (Qubits k) ℂ) =
        (U : Matrix (Qubits k) (Qubits k) ℂ) * site Q.mat i * star (U : Matrix (Qubits k) (Qubits k) ℂ) := by
    intro i
    rw [(D i).second_image, hτ i, hact, hVQ i, site_smul]
  obtain ⟨c, hc, hCU⟩ := same_two_axis_action_scalar C U P Q hP hQ hPQ hCP hCQ
  let i₀ : Fin k := ⟨0, by omega⟩
  refine ⟨absorbPhaseFamily B c hc i₀, τ.symm,
    absorbPhaseFamily_clifford B (fun j => hV (τ.symm j)) c hc i₀, ?_⟩
  rw [absorbPhaseFamily_tensor, Matrix.smul_mul]
  exact hCU

end ExactAmpDich.Hardness.Rigidity


set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ExactAmpDich.OneQubitProof
open QAlgorithms QAlgorithms.Stabilizer

abbrev BMat := Matrix Bool Bool ℂ

def boolQubit : Bool ≃ Qubits 1 where
  toFun b := fun _ => b
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by funext i; fin_cases i; rfl

def lift (M : BMat) : Matrix (Qubits 1) (Qubits 1) ℂ :=
  Matrix.reindex boolQubit boolQubit M

@[simp] lemma lift_apply (M : BMat) (x y : Qubits 1) : lift M x y = M (x 0) (y 0) := rfl

@[simp] lemma lift_mul (M N : BMat) : lift (M * N) = lift M * lift N :=
  (Matrix.reindexRingEquiv ℂ boolQubit).map_mul M N

@[simp] lemma lift_one : lift (1 : BMat) = 1 :=
  (Matrix.reindexRingEquiv ℂ boolQubit).map_one

@[simp] lemma lift_star (M : BMat) : lift (star M) = star (lift M) := by
  apply Matrix.ext
  intro x y
  rfl

@[simp] lemma lift_smul (c : ℂ) (M : BMat) : lift (c • M) = c • lift M := by
  apply Matrix.ext
  intro x y
  rfl

lemma lift_unitary (M : BMat) (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    lift M ∈ Matrix.unitaryGroup (Qubits 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [← lift_star, ← lift_mul, ← lift_one]
  exact congrArg lift (Matrix.mem_unitaryGroup_iff'.mp hM)

def liftUnitary (M : BMat) (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    Matrix.unitaryGroup (Qubits 1) ℂ := ⟨lift M, lift_unitary M hM⟩

def view (V : Matrix.unitaryGroup (Qubits 1) ℂ) : BMat :=
  fun y x => (V : Matrix (Qubits 1) (Qubits 1) ℂ) (fun _ => y) (fun _ => x)

lemma view_unitary (V : Matrix.unitaryGroup (Qubits 1) ℂ) :
    view V ∈ Matrix.unitaryGroup Bool ℂ := by
  have h := V.property
  have he : (Matrix.reindexRingEquiv ℂ boolQubit.symm) (V : Matrix (Qubits 1) (Qubits 1) ℂ) =
      view V := rfl
  rw [Matrix.mem_unitaryGroup_iff']
  have hz := congrArg (Matrix.reindexRingEquiv ℂ boolQubit.symm) (Matrix.mem_unitaryGroup_iff'.mp h)
  have hs : (Matrix.reindexRingEquiv ℂ boolQubit.symm) (star (V : Matrix (Qubits 1) (Qubits 1) ℂ)) = star (view V) := rfl
  simpa only [map_mul, map_one, he, hs] using hz

-- A Hadamard with global phase exp(pi*i/4), avoiding square roots in the finite calculation.
noncomputable def H : BMat := fun y x => if y && x then -((1 + Complex.I) / 2) else (1 + Complex.I) / 2

def S : BMat := QAlgorithms.phaseS

lemma H_unitary : H ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext y x
  cases y <;> cases x <;>
    norm_num [H, Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, Matrix.one_apply,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

lemma S_unitary : S ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext y x
  cases y <;> cases x <;>
    norm_num [S, phaseS, Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, Matrix.one_apply,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im]

def hAxis : Pauli → Pauli | .X => .Z | .Z => .X | p => p

def sAxis : Pauli → Pauli | .X => .Y | .Y => .X | p => p

def yPhase : Pauli → ZMod 4 | .Y => 2 | _ => 0

lemma H_action (p : Pauli) : H * p.mat * star H = Complex.I ^ (yPhase p).val • (hAxis p).mat := by
  have h2 : (2 : ZMod 4).val = 2 := rfl
  cases p <;> ext y x <;> cases y <;> cases x <;>
    norm_num [h2, H, hAxis, yPhase, Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.star_apply, Matrix.one_apply, Complex.ext_iff,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

lemma S_action (p : Pauli) : S * p.mat * star S = Complex.I ^ (yPhase p).val • (sAxis p).mat := by
  have h2 : (2 : ZMod 4).val = 2 := rfl
  cases p <;> ext y x <;> cases y <;> cases x <;>
    norm_num [h2, S, phaseS, sAxis, yPhase, Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.star_apply, Matrix.one_apply, Complex.ext_iff,
      Complex.mul_re, Complex.mul_im]

lemma pauliString_one_lift (P : PauliString 1) :
    P.toMatrix = Complex.I ^ P.phase.val • lift (P.ops 0).mat := by
  apply Matrix.ext
  intro y x
  simp [PauliString.toMatrix, lift, boolQubit]

lemma lift_normalizer_of_action (M : BMat) (hM : M ∈ Matrix.unitaryGroup Bool ℂ)
    (axis : Pauli → Pauli) (phase : Pauli → ZMod 4)
    (hact : ∀ p, M * p.mat * star M = Complex.I ^ (phase p).val • (axis p).mat) :
    liftUnitary M hM ∈ Clifford.normalizer 1 := by
  apply (TractProof.NormalizerFinite.normalizer_iff 1 _).mpr
  intro P
  let Q : PauliString 1 := ⟨P.phase + phase (P.ops 0), fun _ => axis (P.ops 0)⟩
  refine ⟨Q, ?_⟩
  change lift M * P.toMatrix * star (lift M) = Q.toMatrix
  rw [pauliString_one_lift P, Matrix.mul_smul, Matrix.smul_mul]
  rw [← lift_star, ← lift_mul, ← lift_mul, hact, lift_smul, smul_smul]
  rw [TractProof.NormalizerFinite.I_pow_val_add]
  exact (pauliString_one_lift Q).symm

lemma H_normalizer : liftUnitary H H_unitary ∈ Clifford.normalizer 1 :=
  lift_normalizer_of_action H H_unitary hAxis yPhase H_action

lemma S_normalizer : liftUnitary S S_unitary ∈ Clifford.normalizer 1 :=
  lift_normalizer_of_action S S_unitary sAxis yPhase S_action


@[simp] lemma view_liftUnitary (M : BMat) (hM) : view (liftUnitary M hM) = M := by
  apply Matrix.ext
  intro y x
  rfl

@[simp] lemma view_mul (U V : Matrix.unitaryGroup (Qubits 1) ℂ) :
    view (U * V) = view U * view V :=
  (Matrix.reindexRingEquiv ℂ boolQubit.symm).map_mul U.val V.val

@[simp] lemma view_one : view (1 : Matrix.unitaryGroup (Qubits 1) ℂ) = 1 :=
  (Matrix.reindexRingEquiv ℂ boolQubit.symm).map_one

inductive Generator | h | s deriving DecidableEq

noncomputable def generatorUnitary : Generator → Matrix.unitaryGroup (Qubits 1) ℂ
  | .h => liftUnitary H H_unitary
  | .s => liftUnitary S S_unitary

lemma generator_normalizer (g : Generator) : generatorUnitary g ∈ Clifford.normalizer 1 := by
  cases g
  · exact H_normalizer
  · exact S_normalizer

def axis : Fin 3 → Pauli := ![.X, .Y, .Z]

def sign (b : Bool) : ℂ := if b then -1 else 1

@[simp] lemma sign_false : sign false = 1 := rfl
@[simp] lemma sign_true : sign true = -1 := rfl

def signedMatrix (x : Bool × Fin 3) : BMat := sign x.1 • (axis x.2).mat

def generatorAction : Generator → Bool × Fin 3 → Bool × Fin 3
  | .h, (b, a) => (b.xor (decide (a = 1)), ![2, 1, 0] a)
  | .s, (b, a) => (b.xor (decide (a = 1)), ![1, 0, 2] a)

lemma generator_action (g : Generator) (x : Bool × Fin 3) :
    view (generatorUnitary g) * signedMatrix x * star (view (generatorUnitary g)) =
      signedMatrix (generatorAction g x) := by
  have h2 : (2 : ZMod 4).val = 2 := rfl
  obtain ⟨b, a⟩ := x
  cases g <;> cases b <;> fin_cases a <;>
    simp only [generatorUnitary, view_liftUnitary, signedMatrix, Matrix.mul_smul, Matrix.smul_mul]
  all_goals first
    | rw [H_action]
    | rw [S_action]
  all_goals norm_num [generatorAction, signedMatrix, axis, sign, hAxis, sAxis, yPhase, h2, smul_smul]
  all_goals rfl

noncomputable def wordUnitary (w : List Generator) : Matrix.unitaryGroup (Qubits 1) ℂ :=
  (w.map generatorUnitary).prod

def wordAction (w : List Generator) (x : Bool × Fin 3) : Bool × Fin 3 :=
  w.foldr generatorAction x

lemma word_normalizer (w : List Generator) : wordUnitary w ∈ Clifford.normalizer 1 := by
  induction w with
  | nil => exact (Clifford.normalizer 1).one_mem
  | cons g w ih => exact (Clifford.normalizer 1).mul_mem (generator_normalizer g) ih

lemma word_action (w : List Generator) (x : Bool × Fin 3) :
    view (wordUnitary w) * signedMatrix x * star (view (wordUnitary w)) =
      signedMatrix (wordAction w x) := by
  induction w generalizing x with
  | nil => simp [wordUnitary, wordAction]
  | cons g w ih =>
    change view (generatorUnitary g * wordUnitary w) * signedMatrix x *
      star (view (generatorUnitary g * wordUnitary w)) = _
    rw [view_mul, star_mul]
    calc
      _ = view (generatorUnitary g) *
          (view (wordUnitary w) * signedMatrix x * star (view (wordUnitary w))) *
            star (view (generatorUnitary g)) := by simp only [mul_assoc]
      _ = _ := by rw [ih, generator_action]; rfl

def cosetWords : Fin 6 → List Generator :=
  ![[], [.h, .s, .s, .h], [.h], [.s, .s, .h], [.s, .h], [.s, .s, .s, .h]]

def choiceWord (i : Fin 24) : List Generator :=
  cosetWords ⟨i.val / 4, by omega⟩ ++ List.replicate (i.val % 4) .s

lemma choice_transitive : ∀ p q r s : Fin 3, p ≠ q → r ≠ s → ∀ a b : Bool,
    ∃ i : Fin 24, wordAction (choiceWord i) (false, p) = (a, r) ∧
      wordAction (choiceWord i) (false, q) = (b, s) := by decide

def pauliAxis : Pauli → Fin 3 | .I => 0 | .X => 0 | .Y => 1 | .Z => 2

lemma axis_pauli (p : Pauli) (hp : p ≠ .I) : axis (pauliAxis p) = p := by
  cases p <;> simp_all [axis, pauliAxis]

lemma pauliAxis_ne (p q : Pauli) (hp : p ≠ .I) (hq : q ≠ .I) (hne : p ≠ q) :
    pauliAxis p ≠ pauliAxis q := by
  intro h
  exact hne ((axis_pauli p hp).symm.trans ((congrArg axis h).trans (axis_pauli q hq)))

/-- Every ordered pair of signed distinct axes is carried to every other by a one-qubit
Clifford. The finite witness search is over the twenty-four H/S words above. -/
theorem maps_two_axes (P Q R T : Pauli) (hP : P ≠ .I) (hQ : Q ≠ .I)
    (hR : R ≠ .I) (hT : T ≠ .I) (hPQ : P ≠ Q) (hRT : R ≠ T)
    (a b : ℂ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    ∃ V : Matrix.unitaryGroup (Qubits 1) ℂ, V ∈ Clifford.normalizer 1 ∧
      view V * P.mat * star (view V) = a • R.mat ∧
      view V * Q.mat * star (view V) = b • T.mat := by
  obtain ⟨ba, hba⟩ : ∃ ba : Bool, sign ba = a := by
    rcases ha with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ bb : Bool, sign bb = b := by
    rcases hb with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  obtain ⟨i, hiP, hiQ⟩ := choice_transitive (pauliAxis P) (pauliAxis Q)
    (pauliAxis R) (pauliAxis T) (pauliAxis_ne P Q hP hQ hPQ)
    (pauliAxis_ne R T hR hT hRT) ba bb
  refine ⟨wordUnitary (choiceWord i), word_normalizer _, ?_, ?_⟩
  · have hh := word_action (choiceWord i) (false, pauliAxis P)
    rw [hiP] at hh
    simpa only [signedMatrix, sign_false, one_smul,
      axis_pauli P hP, axis_pauli R hR, hba] using hh
  · have hh := word_action (choiceWord i) (false, pauliAxis Q)
    rw [hiQ] at hh
    simpa only [signedMatrix, sign_false, one_smul,
      axis_pauli Q hQ, axis_pauli T hT, hbb] using hh

end ExactAmpDich.OneQubitProof


set_option autoImplicit false

namespace ExactAmpDich.Hardness.Rigidity
open QAlgorithms
open scoped ComplexOrder

/-- The complete published Clifford rigidity lemma, with the exact global matrix equality
and with no extra assumption on the Pauli images or the tensor logarithm. -/
theorem lemma_3_2 (G : Matrix Bool Bool ℂ) (hG : G.PosDef)
    (hBloch : 2 ≤ (Finset.univ.filter fun P : Fin 3 =>
      (G * ![Stabilizer.Pauli.X.mat, Stabilizer.Pauli.Y.mat, Stabilizer.Pauli.Z.mat] P).trace ≠ 0).card)
    {k : ℕ} (hk : 1 ≤ k) (C : Matrix.unitaryGroup (Qubits k) ℂ) (hC : C ∈ Clifford.normalizer k)
    (hcomm : (C : Matrix (Qubits k) (Qubits k) ℂ) * tensorPow G k =
      tensorPow G k * (C : Matrix (Qubits k) (Qubits k) ℂ)) :
    ∃ (V : Fin k → Matrix.unitaryGroup (Qubits 1) ℂ) (σ : Equiv.Perm (Fin k)),
      (∀ i, V i ∈ Clifford.normalizer 1) ∧
      (C : Matrix (Qubits k) (Qubits k) ℂ) =
        tensorProd (fun i y x => (V i : Matrix (Qubits 1) (Qubits 1) ℂ) (fun _ => y) (fun _ => x)) *
          factorPerm σ := by
  classical
  obtain ⟨P, Q, hP, hQ, hPQ, hBP, hBQ⟩ := nonzero_bloch_axes G hBloch
  obtain ⟨τ, D, hτ⟩ := exists_localImageEquiv G hG C hC hcomm P Q hP hQ hPQ hBP hBQ
  have hchoice : ∀ i : Fin k, ∃ V : Matrix.unitaryGroup (Qubits 1) ℂ,
      V ∈ Clifford.normalizer 1 ∧
      oneQubitMatrix (V : Matrix (Qubits 1) (Qubits 1) ℂ) * P.mat *
        star (oneQubitMatrix (V : Matrix (Qubits 1) (Qubits 1) ℂ)) = (D i).a • (D i).first.mat ∧
      oneQubitMatrix (V : Matrix (Qubits 1) (Qubits 1) ℂ) * Q.mat *
        star (oneQubitMatrix (V : Matrix (Qubits 1) (Qubits 1) ℂ)) = (D i).b • (D i).second.mat := by
    intro i
    exact OneQubitProof.maps_two_axes P Q (D i).first (D i).second hP hQ (D i).first_ne_one
      (D i).second_ne_one hPQ (D i).axes_ne (D i).a (D i).b
      (LocalImagePair.first_sign C P Q i (D i)) (LocalImagePair.second_sign C P Q i (D i))
  choose V hV hVP hVQ using hchoice
  exact assemble_local_cliffords hk C P Q hP hQ hPQ τ D hτ V hV hVP hVQ

end ExactAmpDich.Hardness.Rigidity

open ExactAmpDich
open QAlgorithms
open scoped ComplexOrder

theorem solution (G : Matrix Bool Bool ℂ) (hG : G.PosDef)
    (hBloch : 2 ≤ (Finset.univ.filter fun P : Fin 3 =>
      (G * ![Stabilizer.Pauli.X.mat, Stabilizer.Pauli.Y.mat, Stabilizer.Pauli.Z.mat] P).trace ≠ 0).card)
    {k : ℕ} (hk : 1 ≤ k) (C : Matrix.unitaryGroup (Qubits k) ℂ) (hC : C ∈ Clifford.normalizer k)
    (hcomm : (C : Matrix (Qubits k) (Qubits k) ℂ) * tensorPow G k =
      tensorPow G k * (C : Matrix (Qubits k) (Qubits k) ℂ)) :
    ∃ (V : Fin k → Matrix.unitaryGroup (Qubits 1) ℂ) (σ : Equiv.Perm (Fin k)),
      (∀ i, V i ∈ Clifford.normalizer 1) ∧
      (C : Matrix (Qubits k) (Qubits k) ℂ) =
        tensorProd (fun i y x => (V i : Matrix (Qubits 1) (Qubits 1) ℂ) (fun _ => y) (fun _ => x)) *
          factorPerm σ  := ExactAmpDich.Hardness.Rigidity.lemma_3_2 G hG hBloch hk C hC hcomm
