-- Prove2me | solution 1 for CliffordTApprox.Ancilla.composition
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:15:48.676155+00:00
-- url     : https://prove2.me/submissions/ba55df30-c135-40ab-bee9-20d6e5238345

import Definitions.Def_CliffordTApprox_Ancilla_Setting
import Mathlib.Analysis.Complex.Trigonometric

open scoped Matrix
open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12
open CliffordTApprox.Ancilla

lemma circuit_append_unitary (c₁ c₂ : Circuit htcxGateSet (1 + 2)) :
    (c₁ ++ c₂).unitary = c₂.unitary * c₁.unitary := by
  simp [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma initializedMap_mul {n w : ℕ} (A B : Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ) :
    initializedMap (A * B) = A * initializedMap B := by
  ext y x
  rfl

lemma idealMap_mul {n w : ℕ} (U₂ U₁ : Matrix (Qubits n) (Qubits n) ℂ) :
    idealMap (U₂ * U₁) w = idealMap U₂ w * U₁ := by
  ext y x
  simp only [idealMap, Matrix.of_apply, Matrix.mul_apply]
  split_ifs with h <;> simp

lemma mul_idealMap {n w : ℕ} (A : Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ)
    (U : Matrix (Qubits n) (Qubits n) ℂ) :
    A * idealMap U w = initializedMap A * U := by
  ext y x
  change (∑ j, A y j * ((if (qubitsAppendEquiv n w j).2 = (fun _ => false) then U (qubitsAppendEquiv n w j).1 x else 0))) =
    ∑ j, A y (Fin.append j (fun _ => false)) * U j x
  rw [← (qubitsAppendEquiv n w).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero]
  simp [qubitsAppendEquiv]

lemma composition_algebraic_split (c₁ c₂ : Circuit htcxGateSet (1 + 2))
    (U₁ U₂ : Matrix (Qubits 1) (Qubits 1) ℂ) :
    initializedMap (c₁ ++ c₂).unitary - idealMap (U₂ * U₁) 2 =
    c₂.unitary * (initializedMap c₁.unitary - idealMap U₁ 2) +
    (initializedMap c₂.unitary - idealMap U₂ 2) * U₁ := by
  rw [circuit_append_unitary, initializedMap_mul, idealMap_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, mul_idealMap]
  abel

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

lemma frobNorm_sq_eq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    frobNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h_norm : ‖A‖ = (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := Matrix.frobenius_norm_def A
  change ‖A‖ ^ 2 = _
  rw [h_norm]
  have h_nonneg : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _
  have h_pow : ((∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h_nonneg]
    norm_num
  rw [h_pow]
  simp_rw [Real.rpow_two]

lemma trace_re_eq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ((Aᴴ * A).trace).re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Complex.re_sum]
  have h_inner : ∀ j, (∑ i, star (A i j) * A i j).re = ∑ i, ‖A i j‖ ^ 2 := by
    intro j
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (A i j) * A i j = ((‖A i j‖ : ℂ) ^ 2) := RCLike.conj_mul (A i j)
    rw [this, ← Complex.ofReal_pow, Complex.ofReal_re]
  simp_rw [h_inner]
  rw [Finset.sum_comm]

lemma frobNorm_sq_eq_trace_re {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    frobNorm A ^ 2 = ((Aᴴ * A).trace).re := by
  rw [frobNorm_sq_eq, ← trace_re_eq]

lemma frobNorm_sq_eq_trace_mul_self_re {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    frobNorm A ^ 2 = ((A * Aᴴ).trace).re := by
  rw [frobNorm_sq_eq_trace_re, Matrix.trace_mul_comm]

lemma frobNorm_left_unitary_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (V : Matrix m m ℂ) (hV : V ∈ Matrix.unitaryGroup m ℂ) (X : Matrix m n ℂ) :
    frobNorm (V * X) = frobNorm X := by
  have hV_star : Vᴴ * V = (1 : Matrix m m ℂ) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hV
  have h_sq : frobNorm (V * X) ^ 2 = frobNorm X ^ 2 := by
    rw [frobNorm_sq_eq_trace_re, frobNorm_sq_eq_trace_re]
    have h_conj : (V * X)ᴴ = Xᴴ * Vᴴ := Matrix.conjTranspose_mul V X
    rw [h_conj]
    congr 2
    calc (Xᴴ * Vᴴ) * (V * X)
      _ = Xᴴ * (Vᴴ * (V * X)) := by rw [Matrix.mul_assoc]
      _ = Xᴴ * ((Vᴴ * V) * X) := by rw [← Matrix.mul_assoc Vᴴ V X]
      _ = Xᴴ * ((1 : Matrix m m ℂ) * X) := by rw [hV_star]
      _ = Xᴴ * X := by rw [Matrix.one_mul]
  have h1 : 0 ≤ frobNorm (V * X) := norm_nonneg _
  have h2 : 0 ≤ frobNorm X := norm_nonneg _
  exact (sq_eq_sq₀ h1 h2).mp h_sq

lemma frobNorm_right_unitary_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) (Y : Matrix m n ℂ) :
    frobNorm (Y * U) = frobNorm Y := by
  have hU_star : U * Uᴴ = (1 : Matrix n n ℂ) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hU
  have h_sq : frobNorm (Y * U) ^ 2 = frobNorm Y ^ 2 := by
    rw [frobNorm_sq_eq_trace_mul_self_re, frobNorm_sq_eq_trace_mul_self_re]
    have h_conj : (Y * U)ᴴ = Uᴴ * Yᴴ := Matrix.conjTranspose_mul Y U
    rw [h_conj]
    congr 2
    calc (Y * U) * (Uᴴ * Yᴴ)
      _ = Y * (U * (Uᴴ * Yᴴ)) := by rw [Matrix.mul_assoc]
      _ = Y * ((U * Uᴴ) * Yᴴ) := by rw [← Matrix.mul_assoc U Uᴴ Yᴴ]
      _ = Y * ((1 : Matrix n n ℂ) * Yᴴ) := by rw [hU_star]
      _ = Y * Yᴴ := by rw [Matrix.one_mul]
  have h1 : 0 ≤ frobNorm (Y * U) := norm_nonneg _
  have h2 : 0 ≤ frobNorm Y := norm_nonneg _
  exact (sq_eq_sq₀ h1 h2).mp h_sq

lemma hadamard_unitary : hadamardᴴ * hadamard = 1 := by
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    have : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      push_cast; rfl
    calc ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)
      _ = ((Real.sqrt 2 : ℂ) ^ 2)⁻¹ := by ring
      _ = (2 : ℂ)⁻¹ := by rw [this]
      _ = 1 / 2 := by ring
  ext a b
  fin_cases a <;> fin_cases b <;>
  · simp [hadamard, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, h2]
    try ring

lemma gateT_unitary : gateTᴴ * gateT = 1 := by
  have h_norm : ‖Complex.exp (Complex.I * Real.pi / 4)‖ = 1 := by
    have h_eq : Complex.I * (Real.pi : ℂ) / 4 = Complex.I * (Real.pi / 4 : ℝ) := by
      push_cast
      ring
    rw [h_eq]
    exact Complex.norm_exp_I_mul_ofReal (Real.pi / 4)
  have h_exp : (starRingEnd ℂ) (Complex.exp (Complex.I * Real.pi / 4)) *
      Complex.exp (Complex.I * Real.pi / 4) = 1 := by
    have hz : (starRingEnd ℂ) (Complex.exp (Complex.I * Real.pi / 4)) *
        Complex.exp (Complex.I * Real.pi / 4) =
        ((‖Complex.exp (Complex.I * Real.pi / 4)‖ : ℂ) ^ 2) :=
      RCLike.conj_mul _
    rw [hz, h_norm]
    norm_num
  ext a b
  fin_cases a <;> fin_cases b <;>
  · simp [gateT, Matrix.mul_apply, Matrix.diagonal_apply, h_exp]

lemma cnot_unitary : cnotᴴ * cnot = 1 := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
  · simp [cnot, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type]

def qubits1Equiv : Qubits 1 ≃ Bool where
  toFun b := b 0
  invFun x := fun _ => x
  left_inv b := by ext i; fin_cases i; rfl
  right_inv x := rfl

lemma Gate_ofMatrix1_unitary (M : Matrix Bool Bool ℂ) (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    Gate.IsUnitary (Gate.ofMatrix1 M) := by
  dsimp [Gate.IsUnitary, Gate.ofMatrix1]
  rw [Matrix.mem_unitaryGroup_iff']
  have h_mat : (M.submatrix (fun b => b 0) (fun b => b 0)) = M.submatrix qubits1Equiv qubits1Equiv := rfl
  rw [h_mat]
  have h_star : (star (M.submatrix qubits1Equiv qubits1Equiv) : Matrix (Qubits 1) (Qubits 1) ℂ) =
      (star M).submatrix qubits1Equiv qubits1Equiv := by
    ext a b; rfl
  rw [h_star, Matrix.submatrix_mul_equiv]
  have : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.mp hM
  rw [this]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.one_apply, qubits1Equiv.apply_eq_iff_eq]

def qubits2Equiv : Qubits 2 ≃ Bool × Bool where
  toFun b := (b 0, b 1)
  invFun p := fun i => if i.1 = 0 then p.1 else p.2
  left_inv b := by
    ext ⟨i, hi⟩
    interval_cases i <;> rfl
  right_inv p := by ext <;> rfl

lemma Gate_ofMatrix2_unitary (M : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Gate.IsUnitary (Gate.ofMatrix2 M) := by
  dsimp [Gate.IsUnitary, Gate.ofMatrix2]
  rw [Matrix.mem_unitaryGroup_iff']
  have h_mat : (M.submatrix (fun b => (b 0, b 1)) (fun b => (b 0, b 1))) =
      M.submatrix qubits2Equiv qubits2Equiv := rfl
  rw [h_mat]
  have h_star : (star (M.submatrix qubits2Equiv qubits2Equiv) : Matrix (Qubits 2) (Qubits 2) ℂ) =
      (star M).submatrix qubits2Equiv qubits2Equiv := by
    ext a b; rfl
  rw [h_star, Matrix.submatrix_mul_equiv]
  have : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.mp hM
  rw [this]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.one_apply, qubits2Equiv.apply_eq_iff_eq]

lemma htcxGateSet_unitary (g : Gate) (hg : g ∈ htcxGateSet) : Gate.IsUnitary g := by
  simp only [htcxGateSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact Gate_ofMatrix1_unitary hadamard (Matrix.mem_unitaryGroup_iff'.mpr hadamard_unitary)
  · exact Gate_ofMatrix1_unitary gateT (Matrix.mem_unitaryGroup_iff'.mpr gateT_unitary)
  · exact Gate_ofMatrix2_unitary cnot (Matrix.mem_unitaryGroup_iff'.mpr cnot_unitary)

noncomputable def wireEquiv {k n : ℕ} (w : Fin k ↪ Fin n) :
    Fin n ≃ Fin k ⊕ {a : Fin n // a ∉ Set.range w} :=
  (Equiv.sumCompl (fun a => a ∈ Set.range w)).symm.trans
    (((Equiv.ofInjective w w.injective).symm).sumCongr (Equiv.refl _))

noncomputable def qubitsSplitEquiv {k n : ℕ} (w : Fin k ↪ Fin n) :
    Qubits n ≃ Qubits k × ({a : Fin n // a ∉ Set.range w} → Bool) :=
  (Equiv.arrowCongr (wireEquiv w) (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

lemma qubitsSplitEquiv_comp_w {k n : ℕ} (w : Fin k ↪ Fin n)
    (u : Qubits k) (v : {a : Fin n // a ∉ Set.range w} → Bool) :
    (qubitsSplitEquiv w).symm (u, v) ∘ w = u := by
  ext i
  simp [qubitsSplitEquiv, wireEquiv]

lemma qubitsSplitEquiv_apply_not_range {k n : ℕ} (w : Fin k ↪ Fin n)
    (u : Qubits k) (v : {a : Fin n // a ∉ Set.range w} → Bool)
    (a : Fin n) (ha : a ∉ Set.range w) :
    (qubitsSplitEquiv w).symm (u, v) a = v ⟨a, ha⟩ := by
  simp [qubitsSplitEquiv, wireEquiv, ha]

lemma embedOp_one_aux {k n : ℕ} (w : Fin k ↪ Fin n) :
    embedOp (1 : Matrix (Qubits k) (Qubits k) ℂ) w = 1 := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz
    simp
  · rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso
      apply hyz
      ext a
      by_cases ha : a ∈ Set.range w
      · obtain ⟨i, rfl⟩ := ha
        exact congr_fun h2 i
      · exact h1 a ha
    · rfl
    · rfl

lemma conjTranspose_embedOp_aux {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    (embedOp M w)ᴴ = embedOp Mᴴ w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.conjTranspose_apply]
  split_ifs with h1 h2 h3
  · rfl
  · exfalso; apply h2; intro a ha; rw [eq_comm]; exact h1 a ha
  · exfalso; apply h1; intro a ha; rw [eq_comm]; exact h3 a ha
  · simp

lemma embedOp_mul_aux {k n : ℕ} (M N : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp M w * embedOp N w = embedOp (M * N) w := by
  ext y z
  simp only [embedOp, Matrix.mul_apply, Matrix.of_apply]
  by_cases hyz : ∀ a ∉ Set.range w, y a = z a
  · rw [if_pos hyz]
    rw [← (qubitsSplitEquiv w).symm.sum_comp]
    rw [Fintype.sum_prod_type]
    simp_rw [qubitsSplitEquiv_comp_w]
    have h_inner : ∀ u : Qubits k,
        (∑ v : {a // a ∉ Set.range w} → Bool,
          (if ∀ a ∉ Set.range w, y a = (qubitsSplitEquiv w).symm (u, v) a then M (y ∘ w) u else 0) *
          (if ∀ a ∉ Set.range w, (qubitsSplitEquiv w).symm (u, v) a = z a then N u (z ∘ w) else 0)) =
        M (y ∘ w) u * N u (z ∘ w) := by
      intro u
      let v₀ : {a // a ∉ Set.range w} → Bool := fun ⟨a, _⟩ => y a
      have hv₀_y : ∀ a (ha : a ∉ Set.range w), y a = (qubitsSplitEquiv w).symm (u, v₀) a := fun a ha => by
        rw [qubitsSplitEquiv_apply_not_range w u v₀ a ha]
      have hv₀_z : ∀ a (ha : a ∉ Set.range w), (qubitsSplitEquiv w).symm (u, v₀) a = z a := fun a ha => by
        rw [qubitsSplitEquiv_apply_not_range w u v₀ a ha]
        exact hyz a ha
      rw [Fintype.sum_eq_single v₀]
      · rw [if_pos hv₀_y, if_pos hv₀_z]
      · intro v hv
        have : ∃ a ha, y a ≠ v ⟨a, ha⟩ := by
          by_contra hc
          apply hv
          ext ⟨a, ha⟩
          by_contra h_eq
          exact hc ⟨a, ha, Ne.symm h_eq⟩
        rcases this with ⟨a, ha, hne⟩
        have h_cond : ¬ (∀ b ∉ Set.range w, y b = (qubitsSplitEquiv w).symm (u, v) b) := by
          intro hall
          have := hall a ha
          rw [qubitsSplitEquiv_apply_not_range w u v a ha] at this
          exact hne this
        by_cases h_y : ∀ b ∉ Set.range w, y b = (qubitsSplitEquiv w).symm (u, v) b
        · exfalso; exact h_cond h_y
        · rw [if_neg h_y, MulZeroClass.zero_mul]
    simp_rw [h_inner]
  · rw [if_neg hyz]
    have : ∃ a, a ∉ Set.range w ∧ y a ≠ z a := by
      by_contra hc
      apply hyz
      intro a ha
      by_contra hne
      exact hc ⟨a, ha, hne⟩
    rcases this with ⟨a, ha, hne⟩
    apply Finset.sum_eq_zero
    intro j _
    have h_not_both : ¬ ((∀ b ∉ Set.range w, y b = j b) ∧ (∀ b ∉ Set.range w, j b = z b)) := by
      rintro ⟨h1, h2⟩
      exact hne ((h1 a ha).trans (h2 a ha))
    by_cases h1 : ∀ b ∉ Set.range w, y b = j b
    · by_cases h2 : ∀ b ∉ Set.range w, j b = z b
      · exfalso; exact h_not_both ⟨h1, h2⟩
      · rw [if_neg h2, MulZeroClass.mul_zero]
    · rw [if_neg h1, MulZeroClass.zero_mul]

lemma embedOp_mem_unitaryGroup_aux {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n)
    (hM : M ∈ Matrix.unitaryGroup (Qubits k) ℂ) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [Matrix.star_eq_conjTranspose, conjTranspose_embedOp_aux, embedOp_mul_aux]
  have : Mᴴ * M = (1 : Matrix (Qubits k) (Qubits k) ℂ) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hM
  rw [this, embedOp_one_aux]

lemma Circuit_unitary_mem_unitaryGroup_aux {n : ℕ} (c : Circuit htcxGateSet n) :
    c.unitary ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  dsimp [Circuit.unitary]
  apply Submonoid.list_prod_mem
  intro x hx
  rw [List.mem_reverse, List.mem_map] at hx
  rcases hx with ⟨g, _, rfl⟩
  exact embedOp_mem_unitaryGroup_aux g.gate.mat g.wires (htcxGateSet_unitary g.gate g.mem)

theorem solution (c₁ c₂ : Circuit htcxGateSet (1 + 2))
    (U₁ U₂ : Matrix (Qubits 1) (Qubits 1) ℂ) (hU₁ : U₁ ∈ Matrix.unitaryGroup (Qubits 1) ℂ)
    (ε₁ ε₂ : ℝ)
    (h₁ : frobNorm (initializedMap c₁.unitary - idealMap U₁ 2) ≤ ε₁)
    (h₂ : frobNorm (initializedMap c₂.unitary - idealMap U₂ 2) ≤ ε₂) :
    frobNorm (initializedMap (c₁ ++ c₂).unitary - idealMap (U₂ * U₁) 2) ≤ ε₁ + ε₂ := by
  rw [composition_algebraic_split]
  calc frobNorm (c₂.unitary * (initializedMap c₁.unitary - idealMap U₁ 2) +
                 (initializedMap c₂.unitary - idealMap U₂ 2) * U₁)
    _ ≤ frobNorm (c₂.unitary * (initializedMap c₁.unitary - idealMap U₁ 2)) +
        frobNorm ((initializedMap c₂.unitary - idealMap U₂ 2) * U₁) := norm_add_le _ _
    _ = frobNorm (initializedMap c₁.unitary - idealMap U₁ 2) +
        frobNorm (initializedMap c₂.unitary - idealMap U₂ 2) := by
      rw [frobNorm_left_unitary_eq _ (Circuit_unitary_mem_unitaryGroup_aux c₂),
          frobNorm_right_unitary_eq _ hU₁]
    _ ≤ ε₁ + ε₂ := add_le_add h₁ h₂
