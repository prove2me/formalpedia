-- Prove2me | solution 1 for ConstOverheadCompile.Main.decomposition_cnot_h_rotation
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T20:36:25.97266+00:00
-- url     : https://prove2.me/submissions/145b6138-ee08-406c-b805-de074a82ce64

import Definitions.Def_ConstOverheadCompile_Main_GateSets

open ConstOverheadCompile.Main QAlgorithms

private def Gen (n m : ℕ) (U : Matrix (Qubits n) (Qubits n) ℂ) : Prop :=
  ∃ c : Circuit HCnotRotGates n, c.size ≤ m ∧ c.unitary = U

private lemma Gen_one (n : ℕ) : Gen n 0 1 :=
  ⟨[], le_rfl, rfl⟩

private lemma Gen_mono {n m₁ m₂ : ℕ} {U : Matrix (Qubits n) (Qubits n) ℂ}
    (h : Gen n m₁ U) (hm : m₁ ≤ m₂) : Gen n m₂ U := by
  rcases h with ⟨c, hc, rfl⟩
  exact ⟨c, hc.trans hm, rfl⟩

private lemma circuit_unitary_append {S : Set Gate} {n : ℕ} (c₁ c₂ : Circuit S n) :
    (c₁ ++ c₂).unitary = c₂.unitary * c₁.unitary := by
  unfold Circuit.unitary
  rw [List.map_append, List.reverse_append, List.prod_append]

private lemma Gen_mul {n m₁ m₂ : ℕ} {U₁ U₂ : Matrix (Qubits n) (Qubits n) ℂ}
    (h₁ : Gen n m₁ U₁) (h₂ : Gen n m₂ U₂) : Gen n (m₁ + m₂) (U₁ * U₂) := by
  rcases h₁ with ⟨c₁, hs₁, rfl⟩
  rcases h₂ with ⟨c₂, hs₂, rfl⟩
  refine ⟨c₂ ++ c₁, ?_, circuit_unitary_append c₂ c₁⟩
  simp only [Circuit.size, List.length_append] at *
  omega

private lemma embedOp_star {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    star (embedOp M w) = embedOp (star M) w := by
  ext y z
  simp only [Matrix.star_apply, embedOp, Matrix.of_apply]
  have hcond : (∀ a : Fin n, a ∉ Set.range w → z a = y a) ↔
      (∀ a : Fin n, a ∉ Set.range w → y a = z a) :=
    ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
  by_cases hc : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos (hcond.2 hc), if_pos hc]
  · rw [if_neg (mt hcond.1 hc), if_neg hc, star_zero]

private lemma exp_two_pi_mul_I : Complex.exp ((2 * Real.pi : ℂ) * Complex.I) = 1 := by
  have h : ((2 * Real.pi : ℂ) * Complex.I) = ↑Real.pi * Complex.I + ↑Real.pi * Complex.I := by ring
  rw [h, Complex.exp_add, Complex.exp_pi_mul_I]
  norm_num

private lemma hadamard_star : star hadamard = hadamard := by
  ext a b
  cases a <;> cases b <;> simp [hadamard, Complex.conj_ofReal]

private lemma cnot_star : star cnot = cnot := by
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> simp [cnot]

private lemma rot_star (θ : ℝ) : star (rot θ) = rot (2 * Real.pi - θ) := by
  ext a b
  cases a <;> cases b <;> simp [rot, Matrix.star_apply]
  rw [← Complex.exp_conj]
  have hconj : (starRingEnd ℂ) ((θ : ℂ) * Complex.I) = -((θ : ℂ) * Complex.I) := by simp
  rw [hconj]
  have hsplit : (2 * (Real.pi : ℂ) - (θ : ℂ)) * Complex.I =
      (2 * Real.pi : ℂ) * Complex.I + -((θ : ℂ) * Complex.I) := by ring
  rw [hsplit, Complex.exp_add, exp_two_pi_mul_I, one_mul]

private lemma Gen_gate_star {n : ℕ} (g : GateApp HCnotRotGates n) :
    Gen n 1 (star (embedOp g.gate.mat g.wires)) := by
  rcases g with ⟨gate, hmem, wires⟩
  rcases hmem with (rfl | rfl) | ⟨θ, hθ, rfl⟩
  · refine ⟨[⟨Gate.ofMatrix1 hadamard, Or.inl (Set.mem_insert _ _), wires⟩], le_rfl, ?_⟩
    have hs : star (Gate.ofMatrix1 hadamard).mat = (Gate.ofMatrix1 hadamard).mat := by
      dsimp only [Gate.ofMatrix1]
      ext y z; exact congr_fun (congr_fun hadamard_star (y 0)) (z 0)
    simp [Circuit.unitary, embedOp_star, hs]
  · refine ⟨[⟨Gate.ofMatrix2 cnot, Or.inl (Set.mem_insert_of_mem _ rfl), wires⟩], le_rfl, ?_⟩
    have hs : star (Gate.ofMatrix2 cnot).mat = (Gate.ofMatrix2 cnot).mat := by
      dsimp only [Gate.ofMatrix2]
      ext y z; exact congr_fun (congr_fun cnot_star (y 0, y 1)) (z 0, z 1)
    simp [Circuit.unitary, embedOp_star, hs]
  · let θ' : ℝ := 2 * Real.pi - θ
    have hθ' : θ' ∈ Set.Ioo 0 (2 * Real.pi) := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    refine ⟨[⟨Gate.ofMatrix1 (rot θ'), Or.inr ⟨θ', hθ', rfl⟩, wires⟩], le_rfl, ?_⟩
    have hs : star (Gate.ofMatrix1 (rot θ)).mat = (Gate.ofMatrix1 (rot θ')).mat := by
      dsimp only [Gate.ofMatrix1]
      ext y z; exact congr_fun (congr_fun (rot_star θ) (y 0)) (z 0)
    simp [Circuit.unitary, embedOp_star, hs]
    rfl

private lemma Gen_star {n m : ℕ} {U : Matrix (Qubits n) (Qubits n) ℂ} (h : Gen n m U) :
    Gen n m (star U) := by
  rcases h with ⟨c, hs, rfl⟩
  suffices hlen : Gen n (Circuit.size c) (star (Circuit.unitary c)) from Gen_mono hlen hs
  clear hs
  induction c with
  | nil =>
    simpa [Circuit.unitary, Circuit.size] using Gen_one n
  | cons g cs ih =>
    have hcons : Circuit.unitary (g :: cs) =
        Circuit.unitary cs * Circuit.unitary ([g] : Circuit HCnotRotGates n) := by
      simpa using circuit_unitary_append ([g] : Circuit HCnotRotGates n) cs
    have hg : Circuit.unitary ([g] : Circuit HCnotRotGates n) = embedOp g.gate.mat g.wires := by
      simp [Circuit.unitary]
    rw [hcons, StarMul.star_mul, hg]
    have hmul := Gen_mul (Gen_gate_star g) ih
    refine Gen_mono hmul ?_
    simp only [Circuit.size, List.length_cons]
    omega

/-! ### General unitary row/column helper lemmas -/

private lemma unitary_col_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A ∈ Matrix.unitaryGroup ι ℂ) (j : ι) :
    (∑ i : ι, ‖A i j‖ ^ 2) = 1 := by
  have h1 : (star A * A) j j = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'.1 hA, Matrix.one_apply_eq]
  have h2 : ((star A * A) j j).re = ∑ i : ι, ‖A i j‖ ^ 2 := by
    simp [Matrix.mul_apply, Complex.conj_mul', ← Complex.ofReal_pow]
  have h3 := congr_arg Complex.re h1
  simp only [Complex.one_re] at h3
  linarith

private lemma unitary_star_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    star A ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_star]
  exact Matrix.mem_unitaryGroup_iff'.1 hA

private lemma unitary_off_diag_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A ∈ Matrix.unitaryGroup ι ℂ) {i j : ι}
    (hii : A i i = 1) (hij : j ≠ i) : A j i = 0 ∧ A i j = 0 := by
  have col_zero : ∀ {B : Matrix ι ι ℂ}, B ∈ Matrix.unitaryGroup ι ℂ → B i i = 1 → B j i = 0 := by
    intro B hB hBii
    have hsum := unitary_col_sum hB i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
    have hi1 : ‖B i i‖ ^ 2 = 1 := by rw [hBii, norm_one, one_pow]
    have herase : ∑ k ∈ Finset.univ.erase i, ‖B k i‖ ^ 2 = 0 := by linarith
    have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hij, Finset.mem_univ j⟩
    have hj0 : ‖B j i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ‖B k i‖)).1 herase j hmem
    exact norm_eq_zero.1 (sq_eq_zero_iff.1 hj0)
  refine ⟨col_zero hA hii, ?_⟩
  have hstarii : (star A) i i = 1 := by simp [Matrix.star_apply, hii]
  simpa [Matrix.star_apply] using col_zero (unitary_star_mem hA) hstarii

/-! ### Single-qubit lifting and universal 1-qubit synthesis -/

private def wire1 {n : ℕ} (q : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩

private def liftMat1 {n : ℕ} (q : Fin n) (M : Matrix Bool Bool ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  embedOp (Gate.ofMatrix1 M).mat (wire1 q)

private def Gen1 (m : ℕ) (M : Matrix Bool Bool ℂ) : Prop :=
  ∀ (n : ℕ) (q : Fin n), Gen n m (liftMat1 q M)

private lemma liftMat1_apply {n : ℕ} (q : Fin n) (M : Matrix Bool Bool ℂ) (y z : Qubits n) :
    liftMat1 q M y z = if ∀ a : Fin n, a ≠ q → y a = z a then M (y q) (z q) else 0 := by
  unfold liftMat1 embedOp Gate.ofMatrix1
  rw [Matrix.of_apply]
  have hr : ∀ a : Fin n, a ∉ Set.range (wire1 q) ↔ a ≠ q := by
    intro a
    constructor
    · rintro h rfl; exact h ⟨0, rfl⟩
    · rintro h ⟨_, h2⟩; exact h h2.symm
  have hc : (∀ a : Fin n, a ∉ Set.range (wire1 q) → y a = z a) ↔
      (∀ a : Fin n, a ≠ q → y a = z a) := by
    constructor <;> intro h a ha
    · exact h a ((hr a).2 ha)
    · exact h a ((hr a).1 ha)
  by_cases h : ∀ a : Fin n, a ≠ q → y a = z a
  · rw [if_pos (hc.2 h), if_pos h]; rfl
  · rw [if_neg (mt hc.1 h), if_neg h]

private lemma liftMat1_one {n : ℕ} (q : Fin n) : liftMat1 q 1 = 1 := by
  ext y z
  rw [liftMat1_apply]
  conv_rhs => rw [Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · rw [if_neg hyz]
    by_cases hall : ∀ a : Fin n, a ≠ q → y a = z a
    · rw [if_pos hall]
      have hq : y q ≠ z q := by
        intro heq; apply hyz; funext a
        by_cases ha : a = q
        · subst ha; exact heq
        · exact hall a ha
      simp [hq]
    · rw [if_neg hall]

private lemma liftMat1_mul {n : ℕ} (q : Fin n) (M₁ M₂ : Matrix Bool Bool ℂ) :
    liftMat1 q (M₁ * M₂) = liftMat1 q M₁ * liftMat1 q M₂ := by
  ext y z
  rw [liftMat1_apply]
  conv_rhs => rw [Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ≠ q → y a = z a
  · rw [if_pos hyz]
    let w0 : Qubits n := Function.update y q false
    let w1 : Qubits n := Function.update y q true
    have hw01 : w0 ≠ w1 := by
      intro h; have := congr_fun h q; simp [w0, w1] at this
    symm
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w0),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hw01.symm, Finset.mem_univ w1⟩)]
    have hrest : ∑ x ∈ (Finset.univ.erase w0).erase w1, liftMat1 q M₁ y x * liftMat1 q M₂ x z = 0 := by
      refine Finset.sum_eq_zero fun w hw => ?_
      have hw1 : w ≠ w1 := (Finset.mem_erase.1 hw).1
      have hw0 : w ≠ w0 := (Finset.mem_erase.1 (Finset.mem_erase.1 hw).2).1
      have hnot : ¬ (∀ a : Fin n, a ≠ q → y a = w a) := by
        intro hall
        cases hq : w q
        · apply hw0; funext a
          by_cases ha : a = q
          · subst ha; simp [w0, hq]
          · simp [w0, ha, (hall a ha).symm]
        · apply hw1; funext a
          by_cases ha : a = q
          · subst ha; simp [w1, hq]
          · simp [w1, ha, (hall a ha).symm]
      rw [liftMat1_apply q M₁ y w, if_neg hnot, zero_mul]
    rw [hrest, add_zero]
    have hw0y : ∀ a : Fin n, a ≠ q → y a = w0 a := fun a ha => by simp [w0, ha]
    have hw0z : ∀ a : Fin n, a ≠ q → w0 a = z a := fun a ha => by simp [w0, ha, hyz a ha]
    have hw1y : ∀ a : Fin n, a ≠ q → y a = w1 a := fun a ha => by simp [w1, ha]
    have hw1z : ∀ a : Fin n, a ≠ q → w1 a = z a := fun a ha => by simp [w1, ha, hyz a ha]
    rw [liftMat1_apply q M₁ y w0, if_pos hw0y, liftMat1_apply q M₂ w0 z, if_pos hw0z,
      liftMat1_apply q M₁ y w1, if_pos hw1y, liftMat1_apply q M₂ w1 z, if_pos hw1z]
    simp [w0, w1, Matrix.mul_apply, add_comm]
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases hyw : ∀ a : Fin n, a ≠ q → y a = w a
    · have hwz : ¬ (∀ a : Fin n, a ≠ q → w a = z a) := fun hwz =>
        hyz fun a ha => (hyw a ha).trans (hwz a ha)
      rw [liftMat1_apply q M₂ w z, if_neg hwz, mul_zero]
    · rw [liftMat1_apply q M₁ y w, if_neg hyw, zero_mul]

private lemma liftMat1_star {n : ℕ} (q : Fin n) (M : Matrix Bool Bool ℂ) :
    liftMat1 q (star M) = star (liftMat1 q M) := by
  ext y z
  simp only [liftMat1_apply, Matrix.star_apply]
  have hc : (∀ a : Fin n, a ≠ q → z a = y a) ↔ (∀ a : Fin n, a ≠ q → y a = z a) :=
    ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
  by_cases h : ∀ a : Fin n, a ≠ q → y a = z a
  · rw [if_pos h, if_pos (hc.2 h)]
  · rw [if_neg h, if_neg (mt hc.1 h), star_zero]

private lemma liftMat1_unitary {n : ℕ} (q : Fin n) {M : Matrix Bool Bool ℂ}
    (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    liftMat1 q M ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, ← liftMat1_star, ← liftMat1_mul,
    Matrix.mem_unitaryGroup_iff.1 hM, liftMat1_one]

private lemma Gen1_one : Gen1 0 1 := fun n q => by
  rw [liftMat1_one]; exact Gen_one n

private lemma Gen1_mono {m₁ m₂ : ℕ} {M : Matrix Bool Bool ℂ} (h : Gen1 m₁ M) (hm : m₁ ≤ m₂) :
    Gen1 m₂ M := fun n q => Gen_mono (h n q) hm

private lemma Gen1_mul {m₁ m₂ : ℕ} {M₁ M₂ : Matrix Bool Bool ℂ}
    (h₁ : Gen1 m₁ M₁) (h₂ : Gen1 m₂ M₂) : Gen1 (m₁ + m₂) (M₁ * M₂) := fun n q => by
  rw [liftMat1_mul]; exact Gen_mul (h₁ n q) (h₂ n q)

private lemma Gen1_hadamard : Gen1 1 hadamard := fun _ q =>
  ⟨[⟨Gate.ofMatrix1 hadamard, Or.inl (Set.mem_insert _ _), wire1 q⟩], le_rfl, by
    simp [Circuit.unitary, liftMat1]⟩

private lemma Gen1_rot_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) : Gen1 1 (rot θ) := fun _ q =>
  ⟨[⟨Gate.ofMatrix1 (rot θ), Or.inr ⟨θ, hθ, rfl⟩, wire1 q⟩], le_rfl, by
    simp [Circuit.unitary, liftMat1]⟩

private lemma exp_int_two_pi_mul_I (m : ℤ) :
    Complex.exp (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
  have hnat : ∀ k : ℕ, Complex.exp (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h : (((2 * Real.pi * ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
          (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) + (2 * Real.pi : ℂ) * Complex.I := by
        push_cast; ring
      rw [h, Complex.exp_add, ih, exp_two_pi_mul_I, one_mul]
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · simpa using hnat k
  · have h : (((2 * Real.pi * ((- (k : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) =
        -((((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      push_cast; ring
    rw [h, Complex.exp_neg, hnat k, inv_one]

private lemma Gen1_rot (α : ℝ) : Gen1 1 (rot α) := by
  let p : ℝ := 2 * Real.pi
  have hp : 0 < p := by positivity
  let m : ℤ := ⌊α / p⌋
  let α₀ : ℝ := α - p * (m : ℝ)
  have hm_le : p * (m : ℝ) ≤ α := by
    have h := mul_le_mul_of_nonneg_left (Int.floor_le (α / p)) hp.le
    rwa [mul_div_cancel₀ _ hp.ne'] at h
  have hm_lt : α < p * ((m : ℝ) + 1) := by
    have h := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (α / p)) hp
    rwa [mul_div_cancel₀ _ hp.ne'] at h
  have hα₀_nonneg : 0 ≤ α₀ := by linarith
  have hα₀_lt : α₀ < 2 * Real.pi := by change α₀ < p; linarith
  have hrot_eq : rot α = rot α₀ := by
    ext a b
    cases a <;> cases b <;> simp [rot]
    have hsplit : (α : ℂ) * Complex.I =
        (α₀ : ℂ) * Complex.I + (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) := by
      dsimp [α₀, p]; push_cast; ring
    rw [hsplit, Complex.exp_add, exp_int_two_pi_mul_I, mul_one]
  rw [hrot_eq]
  by_cases h0 : α₀ = 0
  · rw [h0]
    have hrot0 : rot 0 = 1 := by ext a b; cases a <;> cases b <;> simp [rot]
    rw [hrot0]
    exact Gen1_mono Gen1_one (by omega)
  · exact Gen1_rot_Ioo ⟨lt_of_le_of_ne hα₀_nonneg (Ne.symm h0), hα₀_lt⟩

private lemma pauliX_mul_self : pauliX * pauliX = 1 := by
  ext a b; cases a <;> cases b <;> simp [pauliX, Matrix.mul_apply]

private lemma pauliX_unitary : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : star pauliX = pauliX := by
    ext a b; cases a <;> cases b <;> simp [pauliX]
  rw [hs, pauliX_mul_self]

private lemma Gen1_pauliX : Gen1 3 pauliX := by
  have heq : hadamard * rot Real.pi * hadamard = pauliX := by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    ext a b
    cases a <;> cases b <;>
      simp [hadamard, rot, pauliX, Matrix.mul_apply, Complex.exp_pi_mul_I] <;>
      field_simp <;> ring_nf <;> simp [h2]
  rw [← heq]
  exact Gen1_mono (Gen1_mul (Gen1_mul Gen1_hadamard (Gen1_rot Real.pi)) Gen1_hadamard) (by omega)

private noncomputable def diag2 (α β : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a =>
    if a then Complex.exp ((β : ℂ) * Complex.I) else Complex.exp ((α : ℂ) * Complex.I)

private noncomputable def scalarPhase (δ : ℝ) : Matrix Bool Bool ℂ :=
  diag2 δ δ

private noncomputable def diagPhase (φ : ℝ) : Matrix Bool Bool ℂ :=
  diag2 (-φ) φ

private noncomputable def ryh (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    match a, b with
    | false, false => Real.cos θ
    | false, true  => -(Real.sin θ : ℂ)
    | true,  false => Real.sin θ
    | true,  true  => Real.cos θ

private lemma diag2_zero : diag2 0 0 = 1 := by
  ext a b; cases a <;> cases b <;> simp [diag2]

private lemma diag2_mul (a₁ b₁ a₂ b₂ : ℝ) :
    diag2 a₁ b₁ * diag2 a₂ b₂ = diag2 (a₁ + a₂) (b₁ + b₂) := by
  ext a b
  cases a <;> cases b <;> simp [diag2, ← Complex.exp_add]
  · congr 1; ring
  · congr 1; ring

private lemma diagPhase_zero : diagPhase 0 = 1 := by
  simp [diagPhase, diag2_zero]

private lemma diagPhase_mul (φ₁ φ₂ : ℝ) :
    diagPhase φ₁ * diagPhase φ₂ = diagPhase (φ₁ + φ₂) := by
  simp only [diagPhase, diag2_mul]
  rw [show -φ₁ + -φ₂ = -(φ₁ + φ₂) by ring]

private lemma scalarPhase_mul (δ₁ δ₂ : ℝ) :
    scalarPhase δ₁ * scalarPhase δ₂ = scalarPhase (δ₁ + δ₂) :=
  diag2_mul δ₁ δ₁ δ₂ δ₂

private lemma scalarPhase_eq_smul (δ : ℝ) :
    scalarPhase δ = Complex.exp ((δ : ℂ) * Complex.I) • (1 : Matrix Bool Bool ℂ) := by
  ext a b; cases a <;> cases b <;> simp [scalarPhase, diag2]

private lemma scalarPhase_comm (δ : ℝ) (X : Matrix Bool Bool ℂ) :
    X * scalarPhase δ = scalarPhase δ * X := by
  rw [scalarPhase_eq_smul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]

private lemma diag2_eq_scalar_mul_diagPhase (θ₀ θ₁ : ℝ) :
    diag2 θ₀ θ₁ = scalarPhase ((θ₀ + θ₁) / 2) * diagPhase ((θ₁ - θ₀) / 2) := by
  simp only [scalarPhase, diagPhase, diag2_mul]
  congr 1 <;> ring

private lemma rot_eq_diag2 (φ : ℝ) : rot φ = diag2 0 φ := by
  ext a b; cases a <;> cases b <;> simp [rot, diag2]

private lemma Gen1_diag2 (α β : ℝ) : Gen1 8 (diag2 α β) := by
  have heq : pauliX * rot α * pauliX * rot β = diag2 α β := by
    ext a b
    cases a <;> cases b <;> simp [pauliX, rot, diag2, Matrix.mul_apply]
  rw [← heq]
  exact Gen1_mono
    (Gen1_mul (Gen1_mul (Gen1_mul Gen1_pauliX (Gen1_rot α)) Gen1_pauliX) (Gen1_rot β))
    (by omega)

private lemma Gen1_scalarPhase (δ : ℝ) : Gen1 8 (scalarPhase δ) :=
  Gen1_diag2 δ δ

private lemma Gen1_diagPhase (φ : ℝ) : Gen1 8 (diagPhase φ) :=
  Gen1_diag2 (-φ) φ

private lemma star_I_eq : star (Complex.I : ℂ) = -Complex.I := by
  simp

private lemma rot_pi_div_two : rot (Real.pi / 2) = phaseS := by
  ext a b
  cases a <;> cases b <;> simp only [rot, phaseS, Matrix.diagonal_apply, ↓reduceIte,
    Bool.true_eq_false, Bool.false_eq_true]
  push_cast
  rw [Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring

private lemma rot_neg_pi_div_two : rot (-(Real.pi / 2)) = star phaseS := by
  ext a b
  cases a <;> cases b <;> simp only [rot, phaseS, Matrix.star_apply, Matrix.diagonal_apply,
    ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, star_zero, star_one, star_I_eq]
  have h : (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) = -(((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_neg]
  have hp : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    push_cast
    rw [Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  rw [hp, Complex.inv_I]

private lemma Gen1_ryh (θ : ℝ) : Gen1 12 (ryh θ) := by
  have heq : rot (Real.pi / 2) * hadamard * diagPhase θ * hadamard * rot (-(Real.pi / 2)) = ryh θ := by
    rw [rot_pi_div_two, rot_neg_pi_div_two]
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    have hexp_pos : Complex.exp ((θ : ℂ) * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hexp_neg : Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
      push_cast
      rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    ext a b
    cases a <;> cases b <;>
      simp only [phaseS, hadamard, diagPhase, diag2, ryh, Matrix.mul_apply, Fintype.sum_bool,
        Matrix.diagonal_apply, Matrix.of_apply, Matrix.star_apply, Bool.true_and, Bool.false_and,
        Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte,
        star_zero, star_one, star_I_eq, hexp_pos, hexp_neg,
        mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] <;>
      field_simp <;> ring_nf <;> simp only [h2, Complex.I_sq] <;> ring
  rw [← heq]
  exact Gen1_mono
    (Gen1_mul (Gen1_mul (Gen1_mul (Gen1_mul (Gen1_rot _) Gen1_hadamard)
      (Gen1_diagPhase θ)) Gen1_hadamard) (Gen1_rot _))
    (by omega)

private lemma ryh_zero : ryh 0 = 1 := by
  ext a b; cases a <;> cases b <;> simp [ryh]

private lemma ryh_mul (θ₁ θ₂ : ℝ) : ryh θ₁ * ryh θ₂ = ryh (θ₁ + θ₂) := by
  ext a b
  cases a <;> cases b <;>
    simp only [ryh, Matrix.mul_apply, Fintype.sum_bool, Matrix.of_apply,
      Real.cos_add, Real.sin_add, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul] <;>
    ring

private lemma pauliX_conj_diagPhase (φ : ℝ) :
    pauliX * diagPhase φ * pauliX = diagPhase (-φ) := by
  ext a b; cases a <;> cases b <;> simp [pauliX, diagPhase, diag2, Matrix.mul_apply]

private lemma pauliX_conj_ryh (θ : ℝ) :
    pauliX * ryh θ * pauliX = ryh (-θ) := by
  ext a b
  cases a <;> cases b <;> simp [pauliX, ryh, Matrix.mul_apply, Real.cos_neg, Real.sin_neg]

/-! ### ZYZ Euler decomposition for U(2) -/

private lemma exp_mul_conj_exp (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) * (starRingEnd ℂ) (Complex.exp ((x : ℂ) * Complex.I)) = 1 := by
  rw [← Complex.exp_conj]
  have h : (starRingEnd ℂ) ((x : ℂ) * Complex.I) = -((x : ℂ) * Complex.I) := by simp
  rw [h, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

private lemma diag2_unitary (α β : ℝ) : diag2 α β ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  cases a <;> cases b <;>
    simp [diag2, Matrix.mul_apply, Matrix.star_apply, exp_mul_conj_exp]

private lemma ryh_unitary (θ : ℝ) : ryh θ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hcs : ((Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2) = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  ext a b
  cases a <;> cases b <;>
    simp only [ryh, Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, Matrix.of_apply,
      Matrix.one_apply, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte,
      Complex.star_def, map_neg, Complex.conj_ofReal]
  · linear_combination hcs
  · ring
  · ring
  · linear_combination hcs

private theorem zyz_decomp (M : Matrix Bool Bool ℂ) (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    ∃ δ α β γ : ℝ, M = scalarPhase δ * diagPhase α * ryh β * diagPhase γ := by
  have hcol0 := unitary_col_sum hM false
  rw [Fintype.sum_bool] at hcol0
  have hu0_ge : -1 ≤ ‖M false false‖ := by linarith [norm_nonneg (M false false)]
  have hu0_le : ‖M false false‖ ≤ 1 := by nlinarith [norm_nonneg (M false false), sq_nonneg ‖M true false‖]
  have hu1_eq : Real.sqrt (1 - ‖M false false‖ ^ 2) = ‖M true false‖ := by
    have hsq : 1 - ‖M false false‖ ^ 2 = ‖M true false‖ ^ 2 := by linarith
    rw [hsq, Real.sqrt_sq (norm_nonneg (M true false))]
  let β : ℝ := Real.arccos ‖M false false‖
  let θ₀ : ℝ := (M false false).arg
  let θ₁ : ℝ := (M true false).arg
  let V₁ : Matrix Bool Bool ℂ := diag2 θ₀ θ₁ * ryh β
  have hV₁ : V₁ ∈ Matrix.unitaryGroup Bool ℂ :=
    Submonoid.mul_mem _ (diag2_unitary θ₀ θ₁) (ryh_unitary β)
  have hV₁_00 : V₁ false false = M false false := by
    simp only [V₁, diag2, ryh, β, θ₀, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply,
      Matrix.of_apply, Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add]
    rw [Real.cos_arccos hu0_ge hu0_le, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I (M false false)
  have hV₁_10 : V₁ true false = M true false := by
    simp only [V₁, diag2, ryh, β, θ₁, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply,
      Matrix.of_apply, Bool.true_eq_false, ↓reduceIte, zero_mul, add_zero]
    rw [Real.sin_arccos, hu1_eq, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I (M true false)
  let W : Matrix Bool Bool ℂ := star V₁ * M
  have hW : W ∈ Matrix.unitaryGroup Bool ℂ :=
    Submonoid.mul_mem _ (unitary_star_mem hV₁) hM
  have hW_00 : W false false = 1 := by
    have hM_left : (star M * M) false false = 1 := by
      rw [Matrix.mem_unitaryGroup_iff'.1 hM]; rfl
    simpa [W, Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, hV₁_00, hV₁_10] using hM_left
  obtain ⟨hW_10, hW_01⟩ := unitary_off_diag_zero hW hW_00 (by decide : true ≠ false)
  have hcol1 := unitary_col_sum hW true
  rw [Fintype.sum_bool, hW_01, norm_zero] at hcol1
  have hW_11_norm : ‖W true true‖ = 1 := by
    nlinarith [norm_nonneg (W true true)]
  let φ : ℝ := (W true true).arg
  have hW_11 : W true true = Complex.exp ((φ : ℂ) * Complex.I) := by
    have hp := Complex.norm_mul_exp_arg_mul_I (W true true)
    rw [hW_11_norm, Complex.ofReal_one, one_mul] at hp
    exact hp.symm
  have hW_rot : W = rot φ := by
    ext a b
    cases a <;> cases b <;> simp [rot, hW_00, hW_01, hW_10, hW_11]
  have hM_eq : M = diag2 θ₀ θ₁ * ryh β * rot φ := by
    calc
      M = (V₁ * star V₁) * M := by rw [Matrix.mem_unitaryGroup_iff.1 hV₁, one_mul]
      _ = V₁ * W := by rw [Matrix.mul_assoc]
      _ = diag2 θ₀ θ₁ * ryh β * rot φ := by rw [hW_rot]
  refine ⟨(θ₀ + θ₁ + φ) / 2, (θ₁ - θ₀) / 2, β, φ / 2, ?_⟩
  rw [hM_eq, diag2_eq_scalar_mul_diagPhase θ₀ θ₁, rot_eq_diag2 φ,
    diag2_eq_scalar_mul_diagPhase 0 φ]
  simp only [zero_add, sub_zero]
  calc
    scalarPhase ((θ₀ + θ₁) / 2) * diagPhase ((θ₁ - θ₀) / 2) * ryh β *
        (scalarPhase (φ / 2) * diagPhase (φ / 2))
      = scalarPhase ((θ₀ + θ₁) / 2) * diagPhase ((θ₁ - θ₀) / 2) *
          (ryh β * scalarPhase (φ / 2)) * diagPhase (φ / 2) := by
        simp only [Matrix.mul_assoc]
    _ = scalarPhase ((θ₀ + θ₁) / 2) * (diagPhase ((θ₁ - θ₀) / 2) * scalarPhase (φ / 2)) *
          ryh β * diagPhase (φ / 2) := by
        rw [scalarPhase_comm (φ / 2) (ryh β)]
        simp only [Matrix.mul_assoc]
    _ = (scalarPhase ((θ₀ + θ₁) / 2) * scalarPhase (φ / 2)) *
          diagPhase ((θ₁ - θ₀) / 2) * ryh β * diagPhase (φ / 2) := by
        rw [scalarPhase_comm (φ / 2) (diagPhase ((θ₁ - θ₀) / 2))]
        simp only [Matrix.mul_assoc]
    _ = scalarPhase ((θ₀ + θ₁ + φ) / 2) * diagPhase ((θ₁ - θ₀) / 2) * ryh β * diagPhase (φ / 2) := by
        rw [scalarPhase_mul]
        have hsum : (θ₀ + θ₁) / 2 + φ / 2 = (θ₀ + θ₁ + φ) / 2 := by ring
        rw [hsum]

private theorem Gen1_unitary {M : Matrix Bool Bool ℂ} (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    Gen1 36 M := by
  obtain ⟨δ, α, β, γ, rfl⟩ := zyz_decomp M hM
  exact Gen1_mono
    (Gen1_mul (Gen1_mul (Gen1_mul (Gen1_scalarPhase δ) (Gen1_diagPhase α))
      (Gen1_ryh β)) (Gen1_diagPhase γ))
    (by omega)

private theorem synth_one_qubit (U : Matrix (Qubits 1) (Qubits 1) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits 1) ℂ) : Gen 1 36 U := by
  let M : Matrix Bool Bool ℂ := Matrix.of fun a b => U (fun _ => a) (fun _ => b)
  have hq1 : ∀ y : Qubits 1, (fun _ : Fin 1 => y 0) = y := fun y => by
    funext i; rw [Fin.eq_zero i]
  have hlift : liftMat1 (0 : Fin 1) M = U := by
    ext y z
    rw [liftMat1_apply, if_pos (fun a ha => absurd (Fin.eq_zero a) ha)]
    simp [M, hq1 y, hq1 z]
  have hM : M ∈ Matrix.unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext a b
    have hu := congr_fun (congr_fun (Matrix.mem_unitaryGroup_iff.1 hU) (fun _ => a)) (fun _ => b)
    have hsum : (M * star M) a b = (U * star U) (fun _ => a) (fun _ => b) := by
      simp only [Matrix.mul_apply, Matrix.star_apply, M]
      rw [Fintype.sum_bool]
      have hfin1 : ∑ x : Qubits 1, U (fun _ => a) x * (star U) x (fun _ => b) =
          U (fun _ => a) (fun _ => true) * (star U) (fun _ => true) (fun _ => b) +
          U (fun _ => a) (fun _ => false) * (star U) (fun _ => false) (fun _ => b) := by
        let e : Bool ≃ Qubits 1 :=
          { toFun := fun c => fun _ => c
            invFun := fun x => x 0
            left_inv := fun _ => rfl
            right_inv := hq1 }
        rw [← Equiv.sum_comp e, Fintype.sum_bool]
        rfl
      simpa [Matrix.star_apply] using hfin1.symm
    rw [hsum, hu]
    have heq : ((fun _ : Fin 1 => a) = (fun _ : Fin 1 => b)) ↔ a = b :=
      ⟨fun h => congr_fun h 0, fun h => by subst h; rfl⟩
    simp [Matrix.one_apply, heq]
  rw [← hlift]
  exact Gen1_unitary hM 1 0

/-! ### Two-qubit synthesis: block-diagonal Barenco controlled-U(2) and 6-step elimination -/

private def q2 (a b : Bool) : Qubits 2 := fun i => if i = 0 then a else b

private def equivQ2 : Bool × Bool ≃ Qubits 2 where
  toFun p := q2 p.1 p.2
  invFun y := (y 0, y 1)
  left_inv := fun ⟨a, b⟩ => by simp [q2]
  right_inv y := by funext i; fin_cases i <;> simp [q2]

private lemma sum_qubits2 {α : Type*} [AddCommMonoid α] (f : Qubits 2 → α) :
    (∑ y : Qubits 2, f y) =
      (f (q2 true true) + f (q2 true false)) + (f (q2 false true) + f (q2 false false)) := by
  rw [← Equiv.sum_comp equivQ2, Fintype.sum_prod_type]
  simp [equivQ2, add_assoc]

private lemma ext_qubits2 {A B : Matrix (Qubits 2) (Qubits 2) ℂ}
    (h : ∀ a b c d : Bool, A (q2 a b) (q2 c d) = B (q2 a b) (q2 c d)) : A = B := by
  ext y z
  have hy : y = q2 (y 0) (y 1) := (equivQ2.right_inv y).symm
  have hz : z = q2 (z 0) (z 1) := (equivQ2.right_inv z).symm
  rw [hy, hz]
  exact h _ _ _ _

private def blockDiag0 (F₀ F₁ : Matrix Bool Bool ℂ) : Matrix (Qubits 2) (Qubits 2) ℂ :=
  Matrix.of fun y z => if y 0 = z 0 then (if y 0 then F₁ (y 1) (z 1) else F₀ (y 1) (z 1)) else 0

private lemma blockDiag0_one : blockDiag0 1 1 = 1 := by
  refine ext_qubits2 fun a b c d => ?_
  have hq : q2 a b = q2 c d ↔ a = c ∧ b = d := by
    constructor
    · intro h; exact ⟨by simpa [q2] using congr_fun h 0, by simpa [q2] using congr_fun h 1⟩
    · rintro ⟨rfl, rfl⟩; rfl
  cases a <;> cases b <;> cases c <;> cases d <;> simp [blockDiag0, q2, Matrix.one_apply, hq]

private lemma blockDiag0_mul (F₀ F₁ G₀ G₁ : Matrix Bool Bool ℂ) :
    blockDiag0 F₀ F₁ * blockDiag0 G₀ G₁ = blockDiag0 (F₀ * G₀) (F₁ * G₁) := by
  refine ext_qubits2 fun a b c d => ?_
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [blockDiag0, Matrix.mul_apply, sum_qubits2, q2]

private lemma blockDiag0_star (F₀ F₁ : Matrix Bool Bool ℂ) :
    star (blockDiag0 F₀ F₁) = blockDiag0 (star F₀) (star F₁) := by
  refine ext_qubits2 fun a b c d => ?_
  cases a <;> cases b <;> cases c <;> cases d <;> simp [blockDiag0, Matrix.star_apply, q2]

private lemma liftMat1_wire1_eq_blockDiag0 (X : Matrix Bool Bool ℂ) :
    liftMat1 (1 : Fin 2) X = blockDiag0 X X := by
  refine ext_qubits2 fun a b c d => ?_
  cases a <;> cases b <;> cases c <;> cases d <;> simp [liftMat1_apply, blockDiag0, q2]

private lemma liftMat1_wire0_rot_eq_blockDiag0 (δ : ℝ) :
    liftMat1 (0 : Fin 2) (rot δ) = blockDiag0 1 (scalarPhase δ) := by
  refine ext_qubits2 fun a b c d => ?_
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [liftMat1_apply, blockDiag0, q2, rot, scalarPhase, diag2]

private def emb01 : Fin 2 ↪ Fin 2 :=
  ⟨![0, 1], by intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢⟩

private def emb10 : Fin 2 ↪ Fin 2 :=
  ⟨![1, 0], by intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢⟩

private def cnot01 : Matrix (Qubits 2) (Qubits 2) ℂ :=
  embedOp (Gate.ofMatrix2 cnot).mat emb01

private def cnot10 : Matrix (Qubits 2) (Qubits 2) ℂ :=
  embedOp (Gate.ofMatrix2 cnot).mat emb10

private lemma Gen_cnot01 : Gen 2 1 cnot01 :=
  ⟨[⟨Gate.ofMatrix2 cnot, Or.inl (Set.mem_insert_of_mem _ rfl), emb01⟩],
    le_rfl, by simp [Circuit.unitary, cnot01]⟩

private lemma Gen_cnot10 : Gen 2 1 cnot10 :=
  ⟨[⟨Gate.ofMatrix2 cnot, Or.inl (Set.mem_insert_of_mem _ rfl), emb10⟩],
    le_rfl, by simp [Circuit.unitary, cnot10]⟩

private lemma range_emb01 (i : Fin 2) : i ∈ Set.range emb01 := by
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

private lemma range_emb10 (i : Fin 2) : i ∈ Set.range emb10 := by
  fin_cases i
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

private lemma cnot01_apply (y z : Qubits 2) :
    cnot01 y z = cnot (y 0, y 1) (z 0, z 1) := by
  unfold cnot01 embedOp Gate.ofMatrix2
  rw [Matrix.of_apply, if_pos (fun i hi => absurd (range_emb01 i) hi)]
  rfl

private lemma cnot10_apply (y z : Qubits 2) :
    cnot10 y z = cnot (y 1, y 0) (z 1, z 0) := by
  unfold cnot10 embedOp Gate.ofMatrix2
  rw [Matrix.of_apply, if_pos (fun i hi => absurd (range_emb10 i) hi)]
  rfl

private lemma cnot01_eq_blockDiag0 : cnot01 = blockDiag0 1 pauliX := by
  refine ext_qubits2 fun a b c d => ?_
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [cnot01_apply, blockDiag0, cnot, pauliX, q2]

private def ctrl01 (M : Matrix Bool Bool ℂ) : Matrix (Qubits 2) (Qubits 2) ℂ :=
  blockDiag0 1 M

private lemma ctrl01_unitary {M : Matrix Bool Bool ℂ} (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    ctrl01 M ∈ Matrix.unitaryGroup (Qubits 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, ctrl01, blockDiag0_star, blockDiag0_mul,
    star_one, one_mul, Matrix.mem_unitaryGroup_iff.1 hM, blockDiag0_one]

private theorem Gen_ctrl01 {M : Matrix Bool Bool ℂ} (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    Gen 2 51 (ctrl01 M) := by
  obtain ⟨δ, α, β, γ, rfl⟩ := zyz_decomp M hM
  let A : Matrix Bool Bool ℂ := diagPhase α * ryh (β / 2)
  let B : Matrix Bool Bool ℂ := ryh (-(β / 2)) * diagPhase (-((γ + α) / 2))
  let C : Matrix Bool Bool ℂ := diagPhase ((γ - α) / 2)
  have hA : Gen 2 20 (liftMat1 1 A) := Gen1_mul (Gen1_diagPhase α) (Gen1_ryh (β / 2)) 2 1
  have hB : Gen 2 20 (liftMat1 1 B) :=
    Gen1_mul (Gen1_ryh (-(β / 2))) (Gen1_diagPhase (-((γ + α) / 2))) 2 1
  have hC : Gen 2 8 (liftMat1 1 C) := Gen1_diagPhase ((γ - α) / 2) 2 1
  have hR : Gen 2 1 (liftMat1 0 (rot δ)) := Gen1_rot δ 2 0
  have hprod : liftMat1 0 (rot δ) * liftMat1 1 A * cnot01 * liftMat1 1 B * cnot01 * liftMat1 1 C =
      ctrl01 (scalarPhase δ * diagPhase α * ryh β * diagPhase γ) := by
    rw [liftMat1_wire0_rot_eq_blockDiag0, liftMat1_wire1_eq_blockDiag0 A,
      liftMat1_wire1_eq_blockDiag0 B, liftMat1_wire1_eq_blockDiag0 C, cnot01_eq_blockDiag0]
    simp only [blockDiag0_mul, one_mul, mul_one, ctrl01]
    congr 1
    · calc
        A * B * C = diagPhase α * (ryh (β / 2) * ryh (-(β / 2))) *
            (diagPhase (-((γ + α) / 2)) * diagPhase ((γ - α) / 2)) := by
          dsimp [A, B, C]; simp only [Matrix.mul_assoc]
        _ = diagPhase α * ryh 0 * diagPhase (-α) := by
          rw [ryh_mul, add_neg_cancel, diagPhase_mul]
          have he : -((γ + α) / 2) + (γ - α) / 2 = -α := by ring
          rw [he]
        _ = 1 := by
          rw [ryh_zero, mul_one, diagPhase_mul, add_neg_cancel, diagPhase_zero]
    · have hXBX : pauliX * B * pauliX = ryh (β / 2) * diagPhase ((γ + α) / 2) := by
        calc
          pauliX * B * pauliX
            = (pauliX * ryh (-(β / 2)) * pauliX) *
                (pauliX * diagPhase (-((γ + α) / 2)) * pauliX) := by
              dsimp [B]
              calc
                pauliX * (ryh (-(β / 2)) * diagPhase (-((γ + α) / 2))) * pauliX
                  = pauliX * ryh (-(β / 2)) * (pauliX * pauliX) *
                      diagPhase (-((γ + α) / 2)) * pauliX := by
                    rw [pauliX_mul_self, mul_one]; simp only [Matrix.mul_assoc]
                _ = (pauliX * ryh (-(β / 2)) * pauliX) *
                      (pauliX * diagPhase (-((γ + α) / 2)) * pauliX) := by
                    simp only [Matrix.mul_assoc]
          _ = ryh (β / 2) * diagPhase ((γ + α) / 2) := by
              rw [pauliX_conj_ryh, pauliX_conj_diagPhase, neg_neg, neg_neg]
      calc
        scalarPhase δ * A * pauliX * B * pauliX * C
          = scalarPhase δ * A * (pauliX * B * pauliX) * C := by simp only [Matrix.mul_assoc]
        _ = scalarPhase δ * diagPhase α * (ryh (β / 2) * ryh (β / 2)) *
              (diagPhase ((γ + α) / 2) * diagPhase ((γ - α) / 2)) := by
            rw [hXBX]; dsimp [A, C]; simp only [Matrix.mul_assoc]
        _ = scalarPhase δ * diagPhase α * ryh β * diagPhase γ := by
            rw [ryh_mul, diagPhase_mul]
            have hb : β / 2 + β / 2 = β := by ring
            have hg : (γ + α) / 2 + (γ - α) / 2 = γ := by ring
            rw [hb, hg]
  rw [← hprod]
  exact Gen_mono
    (Gen_mul (Gen_mul (Gen_mul (Gen_mul (Gen_mul hR hA) Gen_cnot01) hB) Gen_cnot01) hC)
    (by omega)

private def swapMat : Matrix (Qubits 2) (Qubits 2) ℂ :=
  cnot01 * cnot10 * cnot01

private lemma Gen_swapMat : Gen 2 3 swapMat :=
  Gen_mono (Gen_mul (Gen_mul Gen_cnot01 Gen_cnot10) Gen_cnot01) (by omega)

private lemma swapMat_apply (a b c d : Bool) :
    swapMat (q2 a b) (q2 c d) = if a = d ∧ b = c then 1 else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [swapMat, Matrix.mul_apply, sum_qubits2, cnot01_apply, cnot10_apply, cnot, q2]

private lemma swapMat_star : star swapMat = swapMat := by
  refine ext_qubits2 fun a b c d => ?_
  cases a <;> cases b <;> cases c <;> cases d <;> simp [Matrix.star_apply, swapMat_apply]

private lemma swapMat_mul_self : swapMat * swapMat = 1 := by
  refine ext_qubits2 fun a b c d => ?_
  have hq : q2 a b = q2 c d ↔ a = c ∧ b = d := by
    constructor
    · intro h; exact ⟨by simpa [q2] using congr_fun h 0, by simpa [q2] using congr_fun h 1⟩
    · rintro ⟨rfl, rfl⟩; rfl
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [Matrix.mul_apply, sum_qubits2, swapMat_apply, hq]

private lemma swapMat_unitary : swapMat ∈ Matrix.unitaryGroup (Qubits 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, swapMat_star, swapMat_mul_self]

private def T23 (G : Matrix Bool Bool ℂ) : Matrix (Qubits 2) (Qubits 2) ℂ :=
  ctrl01 G

private def T01 (G : Matrix Bool Bool ℂ) : Matrix (Qubits 2) (Qubits 2) ℂ :=
  liftMat1 0 pauliX * ctrl01 G * liftMat1 0 pauliX

private def T13 (G : Matrix Bool Bool ℂ) : Matrix (Qubits 2) (Qubits 2) ℂ :=
  swapMat * ctrl01 G * swapMat

private lemma T23_unitary {G : Matrix Bool Bool ℂ} (hG : G ∈ Matrix.unitaryGroup Bool ℂ) :
    T23 G ∈ Matrix.unitaryGroup (Qubits 2) ℂ :=
  ctrl01_unitary hG

private lemma T01_unitary {G : Matrix Bool Bool ℂ} (hG : G ∈ Matrix.unitaryGroup Bool ℂ) :
    T01 G ∈ Matrix.unitaryGroup (Qubits 2) ℂ :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ (liftMat1_unitary 0 pauliX_unitary) (ctrl01_unitary hG))
    (liftMat1_unitary 0 pauliX_unitary)

private lemma T13_unitary {G : Matrix Bool Bool ℂ} (hG : G ∈ Matrix.unitaryGroup Bool ℂ) :
    T13 G ∈ Matrix.unitaryGroup (Qubits 2) ℂ :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ swapMat_unitary (ctrl01_unitary hG)) swapMat_unitary

private lemma Gen_T23 {G : Matrix Bool Bool ℂ} (hG : G ∈ Matrix.unitaryGroup Bool ℂ) :
    Gen 2 51 (T23 G) :=
  Gen_ctrl01 hG

private lemma Gen_T01 {G : Matrix Bool Bool ℂ} (hG : G ∈ Matrix.unitaryGroup Bool ℂ) :
    Gen 2 57 (T01 G) :=
  Gen_mono (Gen_mul (Gen_mul (Gen1_pauliX 2 0) (Gen_ctrl01 hG)) (Gen1_pauliX 2 0)) (by omega)

private lemma Gen_T13 {G : Matrix Bool Bool ℂ} (hG : G ∈ Matrix.unitaryGroup Bool ℂ) :
    Gen 2 57 (T13 G) :=
  Gen_mono (Gen_mul (Gen_mul Gen_swapMat (Gen_ctrl01 hG)) Gen_swapMat) (by omega)

private lemma liftMat1_0_pauliX_apply (a b c d : Bool) :
    liftMat1 (0 : Fin 2) pauliX (q2 a b) (q2 c d) = if b = d ∧ a ≠ c then 1 else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [liftMat1_apply, pauliX, q2]

private lemma T23_mul_apply (G : Matrix Bool Bool ℂ) (M : Matrix (Qubits 2) (Qubits 2) ℂ)
    (col : Qubits 2) :
    (T23 G * M) (q2 false false) col = M (q2 false false) col ∧
    (T23 G * M) (q2 false true) col = M (q2 false true) col ∧
    (T23 G * M) (q2 true false) col =
      G false false * M (q2 true false) col + G false true * M (q2 true true) col ∧
    (T23 G * M) (q2 true true) col =
      G true false * M (q2 true false) col + G true true * M (q2 true true) col := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [T23, ctrl01, blockDiag0, Matrix.mul_apply, sum_qubits2, q2] <;> ring

private lemma T01_mul_apply (G : Matrix Bool Bool ℂ) (M : Matrix (Qubits 2) (Qubits 2) ℂ)
    (col : Qubits 2) :
    (T01 G * M) (q2 true false) col = M (q2 true false) col ∧
    (T01 G * M) (q2 true true) col = M (q2 true true) col ∧
    (T01 G * M) (q2 false false) col =
      G false false * M (q2 false false) col + G false true * M (q2 false true) col ∧
    (T01 G * M) (q2 false true) col =
      G true false * M (q2 false false) col + G true true * M (q2 false true) col := by
  have hT : ∀ a b c d : Bool,
      T01 G (q2 a b) (q2 c d) =
        if a = c then (if a then (if b = d then 1 else 0) else G b d) else 0 := by
    intro a b c d
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [T01, ctrl01, blockDiag0, Matrix.mul_apply, sum_qubits2, liftMat1_0_pauliX_apply, q2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, sum_qubits2, hT] <;> ring

private lemma T13_mul_apply (G : Matrix Bool Bool ℂ) (M : Matrix (Qubits 2) (Qubits 2) ℂ)
    (col : Qubits 2) :
    (T13 G * M) (q2 false false) col = M (q2 false false) col ∧
    (T13 G * M) (q2 true false) col = M (q2 true false) col ∧
    (T13 G * M) (q2 false true) col =
      G false false * M (q2 false true) col + G false true * M (q2 true true) col ∧
    (T13 G * M) (q2 true true) col =
      G true false * M (q2 false true) col + G true true * M (q2 true true) col := by
  have hT : ∀ a b c d : Bool,
      T13 G (q2 a b) (q2 c d) =
        if b = d then (if b then G a c else (if a = c then 1 else 0)) else 0 := by
    intro a b c d
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [T13, ctrl01, blockDiag0, Matrix.mul_apply, sum_qubits2, swapMat_apply, q2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, sum_qubits2, hT] <;> ring

/-! ### Givens rotations on ℂ² and 6-step elimination for U(4) -/

private noncomputable def givensMat (c s : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j =>
    match i, j with
    | false, false => (starRingEnd ℂ) c
    | false, true  => (starRingEnd ℂ) s
    | true,  false => -s
    | true,  true  => c

private lemma givensMat_unitary {c s : ℂ}
    (hcs : (starRingEnd ℂ) c * c + (starRingEnd ℂ) s * s = 1) :
    givensMat c s ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  cases i <;> cases j <;>
    simp only [givensMat, Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, Matrix.of_apply,
      Matrix.one_apply, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte,
      Complex.star_def, map_neg, starRingEnd_self_apply]
  · linear_combination hcs
  · ring
  · ring
  · linear_combination hcs

private lemma givens_zero_second (a b : ℂ) :
    ∃ G : Matrix Bool Bool ℂ, G ∈ Matrix.unitaryGroup Bool ℂ ∧
      G false false * a + G false true * b = (Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) : ℂ) ∧
      G true false * a + G true true * b = 0 := by
  let r : ℝ := Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2)
  by_cases hr : r = 0
  · have hsum_nonneg : 0 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by positivity
    have hsq0 : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 0 :=
      (Real.sqrt_eq_zero hsum_nonneg).1 hr
    have ha0 : a = 0 := norm_eq_zero.1 (by nlinarith [norm_nonneg a, sq_nonneg ‖b‖])
    have hb0 : b = 0 := norm_eq_zero.1 (by nlinarith [norm_nonneg b, sq_nonneg ‖a‖])
    refine ⟨1, Submonoid.one_mem _, ?_, ?_⟩
    · simp [ha0, hb0]
    · simp [ha0, hb0]
  · have hr_pos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
    have hrc_ne : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    let c : ℂ := a / (r : ℂ)
    let s : ℂ := b / (r : ℂ)
    have hr_sq : r ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := Real.sq_sqrt (by positivity)
    have hcs_norm : ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1 := by
      have hc : ‖c‖ = ‖a‖ / r := by
        simp [c, Real.norm_eq_abs, abs_of_pos hr_pos]
      have hs : ‖s‖ = ‖b‖ / r := by
        simp [s, Real.norm_eq_abs, abs_of_pos hr_pos]
      rw [hc, hs, div_pow, div_pow, ← add_div, ← hr_sq, div_self (pow_ne_zero 2 hr)]
    have hcs : (starRingEnd ℂ) c * c + (starRingEnd ℂ) s * s = 1 := by
      rw [Complex.conj_mul', Complex.conj_mul']
      exact_mod_cast hcs_norm
    have ha_eq : a = c * (r : ℂ) := (div_mul_cancel₀ a hrc_ne).symm
    have hb_eq : b = s * (r : ℂ) := (div_mul_cancel₀ b hrc_ne).symm
    refine ⟨givensMat c s, givensMat_unitary hcs, ?_, ?_⟩
    · simp only [givensMat, Matrix.of_apply]
      calc
        (starRingEnd ℂ) c * a + (starRingEnd ℂ) s * b
          = ((starRingEnd ℂ) c * c + (starRingEnd ℂ) s * s) * (r : ℂ) := by
            nth_rw 1 [ha_eq, hb_eq]; ring
        _ = (r : ℂ) := by rw [hcs, one_mul]
    · simp only [givensMat, Matrix.of_apply]
      nth_rw 1 [ha_eq, hb_eq]
      ring

private lemma givens_zero_first (a b : ℂ) :
    ∃ G : Matrix Bool Bool ℂ, G ∈ Matrix.unitaryGroup Bool ℂ ∧
      G false false * a + G false true * b = 0 ∧
      G true false * a + G true true * b = (Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) : ℂ) := by
  obtain ⟨G₀, hG₀, h1, h2⟩ := givens_zero_second b a
  refine ⟨pauliX * G₀ * pauliX,
    Submonoid.mul_mem _ (Submonoid.mul_mem _ pauliX_unitary hG₀) pauliX_unitary, ?_, ?_⟩
  · have h : (pauliX * G₀ * pauliX) false false * a + (pauliX * G₀ * pauliX) false true * b =
        G₀ true false * b + G₀ true true * a := by
      simp [pauliX, Matrix.mul_apply]; ring
    rw [h, h2]
  · have h : (pauliX * G₀ * pauliX) true false * a + (pauliX * G₀ * pauliX) true true * b =
        G₀ false false * b + G₀ false true * a := by
      simp [pauliX, Matrix.mul_apply]; ring
    rw [h, h1, add_comm (‖a‖ ^ 2)]

private theorem synth_two_qubit (U : Matrix (Qubits 2) (Qubits 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits 2) ℂ) : Gen 2 324 U := by
  -- Step 1: zero (10, 00) via T23
  obtain ⟨G₁, hG₁, hG₁_0, _⟩ :=
    givens_zero_first (U (q2 true false) (q2 false false)) (U (q2 true true) (q2 false false))
  let M₁ := T23 G₁ * U
  have hM₁_u : M₁ ∈ Matrix.unitaryGroup (Qubits 2) ℂ := Submonoid.mul_mem _ (T23_unitary hG₁) hU
  have hM₁_20 : M₁ (q2 true false) (q2 false false) = 0 := by
    dsimp only [M₁]
    rw [(T23_mul_apply G₁ U (q2 false false)).2.2.1, hG₁_0]
  -- Step 2: zero (11, 00) via T13 (preserving (10, 00) = 0)
  obtain ⟨G₂, hG₂, _, hG₂_0⟩ :=
    givens_zero_second (M₁ (q2 false true) (q2 false false)) (M₁ (q2 true true) (q2 false false))
  let M₂ := T13 G₂ * M₁
  have hM₂_u : M₂ ∈ Matrix.unitaryGroup (Qubits 2) ℂ := Submonoid.mul_mem _ (T13_unitary hG₂) hM₁_u
  have hM₂_20 : M₂ (q2 true false) (q2 false false) = 0 := by
    dsimp only [M₂]
    rw [(T13_mul_apply G₂ M₁ (q2 false false)).2.1, hM₁_20]
  have hM₂_30 : M₂ (q2 true true) (q2 false false) = 0 := by
    dsimp only [M₂]
    rw [(T13_mul_apply G₂ M₁ (q2 false false)).2.2.2, hG₂_0]
  -- Step 3: zero (01, 00) and normalize (00, 00) = 1 via T01
  obtain ⟨G₃, hG₃, hG₃_r, _⟩ :=
    givens_zero_second (M₂ (q2 false false) (q2 false false)) (M₂ (q2 false true) (q2 false false))
  let M₃ := T01 G₃ * M₂
  have hM₃_u : M₃ ∈ Matrix.unitaryGroup (Qubits 2) ℂ := Submonoid.mul_mem _ (T01_unitary hG₃) hM₂_u
  have hM₃_00 : M₃ (q2 false false) (q2 false false) = 1 := by
    have hsum := unitary_col_sum hM₂_u (q2 false false)
    rw [sum_qubits2, hM₂_20, hM₂_30, norm_zero] at hsum
    have hsq : ‖M₂ (q2 false false) (q2 false false)‖ ^ 2 +
        ‖M₂ (q2 false true) (q2 false false)‖ ^ 2 = 1 := by linarith
    dsimp only [M₃]
    rw [(T01_mul_apply G₃ M₂ (q2 false false)).2.2.1, hG₃_r, hsq, Real.sqrt_one, Complex.ofReal_one]
  -- Step 4: zero (10, 01) via T23 (fixing row/col 00)
  obtain ⟨G₄, hG₄, hG₄_0, _⟩ :=
    givens_zero_first (M₃ (q2 true false) (q2 false true)) (M₃ (q2 true true) (q2 false true))
  let M₄ := T23 G₄ * M₃
  have hM₄_u : M₄ ∈ Matrix.unitaryGroup (Qubits 2) ℂ := Submonoid.mul_mem _ (T23_unitary hG₄) hM₃_u
  have hM₄_00 : M₄ (q2 false false) (q2 false false) = 1 := by
    dsimp only [M₄]
    rw [(T23_mul_apply G₄ M₃ (q2 false false)).1, hM₃_00]
  have hM₄_21 : M₄ (q2 true false) (q2 false true) = 0 := by
    dsimp only [M₄]
    rw [(T23_mul_apply G₄ M₃ (q2 false true)).2.2.1, hG₄_0]
  -- Step 5: zero (11, 01) and normalize (01, 01) = 1 via T13 (fixing row/col 00 and (10, 01) = 0)
  obtain ⟨G₅, hG₅, hG₅_r, _⟩ :=
    givens_zero_second (M₄ (q2 false true) (q2 false true)) (M₄ (q2 true true) (q2 false true))
  let M₅ := T13 G₅ * M₄
  have hM₅_u : M₅ ∈ Matrix.unitaryGroup (Qubits 2) ℂ := Submonoid.mul_mem _ (T13_unitary hG₅) hM₄_u
  have hM₅_00 : M₅ (q2 false false) (q2 false false) = 1 := by
    dsimp only [M₅]
    rw [(T13_mul_apply G₅ M₄ (q2 false false)).1, hM₄_00]
  have hM₅_11 : M₅ (q2 false true) (q2 false true) = 1 := by
    have hM₄_01 : M₄ (q2 false false) (q2 false true) = 0 :=
      (unitary_off_diag_zero hM₄_u hM₄_00 (by intro h; have := congr_fun h 1; simp [q2] at this)).2
    have hsum := unitary_col_sum hM₄_u (q2 false true)
    rw [sum_qubits2, hM₄_01, hM₄_21, norm_zero] at hsum
    have hsq : ‖M₄ (q2 false true) (q2 false true)‖ ^ 2 +
        ‖M₄ (q2 true true) (q2 false true)‖ ^ 2 = 1 := by linarith
    dsimp only [M₅]
    rw [(T13_mul_apply G₅ M₄ (q2 false true)).2.2.1, hG₅_r, hsq, Real.sqrt_one, Complex.ofReal_one]
  -- Step 6: M₅ = blockDiag0 1 W for W ∈ U(2); multiply by T23 (star W)
  let W : Matrix Bool Bool ℂ := Matrix.of fun a b => M₅ (q2 true a) (q2 true b)
  have hM₅_block : M₅ = blockDiag0 1 W := by
    have hne01 : q2 false true ≠ q2 false false := by intro h; have := congr_fun h 1; simp [q2] at this
    have hne10_0 : q2 true false ≠ q2 false false := by intro h; have := congr_fun h 0; simp [q2] at this
    have hne11_0 : q2 true true ≠ q2 false false := by intro h; have := congr_fun h 0; simp [q2] at this
    have hne10_1 : q2 true false ≠ q2 false true := by intro h; have := congr_fun h 0; simp [q2] at this
    have hne11_1 : q2 true true ≠ q2 false true := by intro h; have := congr_fun h 0; simp [q2] at this
    obtain ⟨h01_00, h00_01⟩ := unitary_off_diag_zero hM₅_u hM₅_00 hne01
    obtain ⟨h10_00, h00_10⟩ := unitary_off_diag_zero hM₅_u hM₅_00 hne10_0
    obtain ⟨h11_00, h00_11⟩ := unitary_off_diag_zero hM₅_u hM₅_00 hne11_0
    obtain ⟨h10_01, h01_10⟩ := unitary_off_diag_zero hM₅_u hM₅_11 hne10_1
    obtain ⟨h11_01, h01_11⟩ := unitary_off_diag_zero hM₅_u hM₅_11 hne11_1
    refine ext_qubits2 fun a b c d => ?_
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [blockDiag0, W, q2, hM₅_00, hM₅_11,
        h01_00, h00_01, h10_00, h00_10, h11_00, h00_11, h10_01, h01_10, h11_01, h01_11]
  have hW_u : W ∈ Matrix.unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hu := Matrix.mem_unitaryGroup_iff.1 hM₅_u
    rw [hM₅_block, blockDiag0_star, blockDiag0_mul, star_one, one_mul, ← blockDiag0_one] at hu
    ext a b
    have hab := congr_fun (congr_fun hu (q2 true a)) (q2 true b)
    simpa [blockDiag0, q2, Matrix.one_apply] using hab
  let G : Matrix (Qubits 2) (Qubits 2) ℂ :=
    T23 (star W) * T13 G₅ * T23 G₄ * T01 G₃ * T13 G₂ * T23 G₁
  have hG_u : G ∈ Matrix.unitaryGroup (Qubits 2) ℂ :=
    Submonoid.mul_mem _
      (Submonoid.mul_mem _
        (Submonoid.mul_mem _
          (Submonoid.mul_mem _
            (Submonoid.mul_mem _ (T23_unitary (unitary_star_mem hW_u)) (T13_unitary hG₅))
            (T23_unitary hG₄))
          (T01_unitary hG₃))
        (T13_unitary hG₂))
      (T23_unitary hG₁)
  have hG_gen : Gen 2 324 G :=
    Gen_mono
      (Gen_mul
        (Gen_mul
          (Gen_mul
            (Gen_mul
              (Gen_mul (Gen_T23 (unitary_star_mem hW_u)) (Gen_T13 hG₅))
              (Gen_T23 hG₄))
            (Gen_T01 hG₃))
          (Gen_T13 hG₂))
        (Gen_T23 hG₁))
      (by omega)
  have hGU : G * U = 1 := by
    calc
      G * U = T23 (star W) * M₅ := by
        dsimp [G, M₅, M₄, M₃, M₂, M₁]
        simp only [Matrix.mul_assoc]
      _ = blockDiag0 1 (star W) * blockDiag0 1 W := by rw [T23, ctrl01, hM₅_block]
      _ = 1 := by
        rw [blockDiag0_mul, one_mul, Matrix.mem_unitaryGroup_iff'.1 hW_u, blockDiag0_one]
  have hU_eq : U = star G := by
    calc
      U = (star G * G) * U := by rw [Matrix.mem_unitaryGroup_iff'.1 hG_u, one_mul]
      _ = star G * (G * U) := by rw [Matrix.mul_assoc]
      _ = star G := by rw [hGU, mul_one]
  rw [hU_eq]
  exact Gen_star hG_gen

theorem solution :
    ∃ N : ℕ, ∀ k : ℕ, (k = 1 ∨ k = 2) →
      ∀ U : Matrix (Qubits k) (Qubits k) ℂ, U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
        ∃ c : Circuit HCnotRotGates k, c.size ≤ N ∧ c.unitary = U := by
  refine ⟨324, fun k hk U hU => ?_⟩
  rcases hk with rfl | rfl
  · exact Gen_mono (synth_one_qubit U hU) (by omega)
  · exact synth_two_qubit U hU
