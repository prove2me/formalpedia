-- Prove2me | solution 1 for GL2QFT.Circuits.gamma_mark_phase_and_unmark
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T07:06:07.323793+00:00
-- url     : https://prove2.me/submissions/9cc88f5b-b558-4cdf-9a46-34b674520653

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

set_option autoImplicit false

noncomputable section

open Classical

namespace GL2QFT_GammaMark_Aux

open GL2QFT GL2QFT.Circuits QAlgorithms QAlgorithms.Complexity

/-! ### Section 1: Elementary quantum gates on basis states and Clifford+T Toffoli -/

@[simp]
lemma wire1_apply {n : ℕ} (i : Fin n) (x : Fin 1) : wire1 i x = i := rfl

@[simp]
lemma wire2_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j) : wire2 i j hij 0 = i := rfl

@[simp]
lemma wire2_one {n : ℕ} (i j : Fin n) (hij : i ≠ j) : wire2 i j hij 1 = j := rfl

lemma ket_apply {ι : Type} [DecidableEq ι] (i j : ι) :
    (ket i : EuclideanSpace ℂ ι) j = if j = i then 1 else 0 := by
  simp [ket, PiLp.single_apply]

lemma act_add {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) :
    act M (u + v) = act M u + act M v := by
  apply WithLp.ofLp_injective
  funext y
  simp [act, Matrix.mulVec_add]

lemma act_smul {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (c : ℂ) (u : EuclideanSpace ℂ ι) :
    act M (c • u) = c • act M u := by
  apply WithLp.ofLp_injective
  funext y
  simp [act, Matrix.mulVec_smul]

lemma act_ket {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (q : ι) :
    act M (ket q) = WithLp.toLp 2 (fun y => M y q) := by
  apply WithLp.ofLp_injective
  funext y
  simp only [act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, ket_apply]
  rw [Finset.sum_eq_single q]
  · simp
  · intro z _ hz; simp [hz]
  · intro hm; exact absurd (Finset.mem_univ q) hm

lemma matrix_eq_of_act_ket {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (h : ∀ q : ι, act A (ket q) = act B (ket q)) : A = B := by
  ext y q
  have hy := congrArg (fun v : EuclideanSpace ℂ ι => v y) (h q)
  simpa [act_ket] using hy

lemma act_mul {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  apply WithLp.ofLp_injective
  simp [act, Matrix.mulVec_mulVec]

lemma act_permMat {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ι) (q : ι) :
    act (permMat f) (ket q) = ket (f q) := by
  apply WithLp.ofLp_injective
  funext y
  simp [act_ket, permMat, ket_apply]

lemma permMat_mul {X Y Z : Type} [Fintype Y] [DecidableEq Y] [DecidableEq Z]
    (g : Y → Z) (f : X → Y) :
    permMat g * permMat f = permMat (g ∘ f) := by
  ext z x
  simp only [Matrix.mul_apply, permMat, Matrix.of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro y _ hy; simp [hy]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma permMat_id {X : Type} [DecidableEq X] :
    permMat (id : X → X) = 1 := by
  ext y x
  simp [permMat, Matrix.one_apply]

lemma act_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (q : ι) :
    act (Matrix.diagonal d) (ket q) = d q • ket q := by
  apply WithLp.ofLp_injective
  funext y
  by_cases hy : y = q
  · subst hy; simp [act_ket, ket_apply]
  · simp [act_ket, ket_apply, hy]

lemma circUnitary_nil {n : ℕ} : circUnitary ([] : List (Instr n)) = 1 := by
  simp [circUnitary, Circuit.unitary]

lemma circUnitary_cons {n : ℕ} (g : Instr n) (c : List (Instr n)) :
    circUnitary (g :: c) = circUnitary c * circUnitary [g] := by
  simp [circUnitary, Circuit.unitary]

lemma circUnitary_append {n : ℕ} (c₁ c₂ : List (Instr n)) :
    circUnitary (c₁ ++ c₂) = circUnitary c₂ * circUnitary c₁ := by
  simp [circUnitary, Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma embedOp_wire1 {n : ℕ} (M : Matrix Bool Bool ℂ) (i : Fin n) (y z : Qubits n) :
    embedOp (Gate.ofMatrix1 M).mat (wire1 i) y z =
      if ∀ a : Fin n, a ≠ i → y a = z a then M (y i) (z i) else 0 := by
  unfold embedOp Gate.ofMatrix1
  rw [Matrix.of_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range (wire1 i) → y a = z a) ↔ (∀ a : Fin n, a ≠ i → y a = z a) := by
    constructor
    · intro h a ha; exact h a (by rintro ⟨x, rfl⟩; exact ha rfl)
    · intro h a ha; exact h a (fun heq => ha ⟨0, heq.symm⟩)
  by_cases h : ∀ a : Fin n, a ≠ i → y a = z a
  · rw [if_pos (hiff.mpr h), if_pos h]
    rfl
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

lemma embedOp_wire2 {n : ℕ} (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) (i j : Fin n) (hij : i ≠ j)
    (y z : Qubits n) :
    embedOp (Gate.ofMatrix2 M).mat (wire2 i j hij) y z =
      if ∀ a : Fin n, a ≠ i → a ≠ j → y a = z a then M (y i, y j) (z i, z j) else 0 := by
  unfold embedOp Gate.ofMatrix2
  rw [Matrix.of_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range (wire2 i j hij) → y a = z a) ↔
      (∀ a : Fin n, a ≠ i → a ≠ j → y a = z a) := by
    constructor
    · intro h a hai haj
      apply h a
      rintro ⟨b, hb⟩
      fin_cases b
      · exact hai hb.symm
      · exact haj hb.symm
    · intro h a ha
      exact h a (fun heq => ha ⟨0, heq.symm⟩) (fun heq => ha ⟨1, heq.symm⟩)
  by_cases h : ∀ a : Fin n, a ≠ i → a ≠ j → y a = z a
  · rw [if_pos (hiff.mpr h), if_pos h]
    rfl
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

lemma instr_x_unitary {n : ℕ} (i : Fin n) :
    circUnitary [.x i] = permMat (fun q : Qubits n => Function.update q i (!q i)) := by
  ext y z
  simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one, instrApp]
  rw [embedOp_wire1]
  simp only [pauliX, permMat, Matrix.of_apply]
  by_cases hy : y = Function.update z i (!z i)
  · subst hy
    rw [if_pos rfl, if_pos (fun a ha => by simp [ha])]
    cases hzi : z i <;> simp
  · rw [if_neg hy]
    by_cases h1 : ∀ a : Fin n, a ≠ i → y a = z a
    · rw [if_pos h1]
      by_cases h2 : y i = z i
      · rw [if_pos h2]
      · exfalso
        apply hy
        funext a
        by_cases hai : a = i
        · subst hai
          cases hza : z a <;> cases hya : y a <;> simp_all
        · simp [hai, h1 a hai]
    · rw [if_neg h1]

lemma instr_cnot_unitary {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    circUnitary [.cnot i j hij] =
      permMat (fun q : Qubits n => Function.update q j (xor (q j) (q i))) := by
  ext y z
  simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one, instrApp]
  rw [embedOp_wire2]
  simp only [cnot, permMat, Matrix.of_apply]
  by_cases hy : y = Function.update z j (xor (z j) (z i))
  · subst hy
    rw [if_pos rfl, if_pos (fun a _ haj => by simp [haj])]
    simp [hij]
  · rw [if_neg hy]
    by_cases h1 : ∀ a : Fin n, a ≠ i → a ≠ j → y a = z a
    · rw [if_pos h1]
      by_cases h2 : y i = z i ∧ y j = xor (z j) (z i)
      · exfalso
        apply hy
        funext a
        by_cases haj : a = j
        · subst haj; simpa using h2.2
        · by_cases hai : a = i
          · subst hai; simpa [haj] using h2.1
          · simpa [haj] using h1 a hai haj
      · rw [if_neg h2]
    · rw [if_neg h1]

lemma instr_s_unitary {n : ℕ} (i : Fin n) :
    circUnitary [.s i] = Matrix.diagonal (fun q : Qubits n => if q i then Complex.I else 1) := by
  ext y z
  simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one, instrApp]
  rw [embedOp_wire1]
  simp only [phaseS, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz
    rw [if_pos rfl, if_pos (fun _ _ => rfl), if_pos rfl]
  · rw [if_neg hyz]
    by_cases h1 : ∀ a : Fin n, a ≠ i → y a = z a
    · rw [if_pos h1]
      have hne : y i ≠ z i := by
        intro heq
        apply hyz
        funext a
        by_cases hai : a = i
        · subst hai; exact heq
        · exact h1 a hai
      rw [if_neg hne]
    · rw [if_neg h1]

lemma instr_s_s_unitary {n : ℕ} (i : Fin n) :
    circUnitary ([.s i, .s i] : List (Instr n)) =
      Matrix.diagonal (fun q : Qubits n => if q i then (-1 : ℂ) else 1) := by
  have h : ([.s i, .s i] : List (Instr n)) = [.s i] ++ [.s i] := rfl
  rw [h, circUnitary_append, instr_s_unitary]
  ext y z
  by_cases hyz : y = z
  · subst hyz
    cases hyi : y i <;> simp [hyi]
  · simp [hyz]

lemma instr_t_unitary {n : ℕ} (i : Fin n) :
    circUnitary [.t i] =
      Matrix.diagonal (fun q : Qubits n => if q i then Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  ext y z
  simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one, instrApp]
  rw [embedOp_wire1]
  simp only [gateT, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz
    rw [if_pos rfl, if_pos (fun _ _ => rfl), if_pos rfl]
  · rw [if_neg hyz]
    by_cases h1 : ∀ a : Fin n, a ≠ i → y a = z a
    · rw [if_pos h1]
      have hne : y i ≠ z i := by
        intro heq
        apply hyz
        funext a
        by_cases hai : a = i
        · subst hai; exact heq
        · exact h1 a hai
      rw [if_neg hne]
    · rw [if_neg h1]

lemma act_h_ket {n : ℕ} (i : Fin n) (q : Qubits n) :
    act (circUnitary [.h i]) (ket q) =
      ((Real.sqrt 2)⁻¹ : ℂ) •
        (ket (Function.update q i false) +
          (if q i then (-1 : ℂ) else 1) • ket (Function.update q i true)) := by
  apply WithLp.ofLp_injective
  funext y
  simp only [act_ket, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, ket_apply]
  simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one, instrApp]
  rw [embedOp_wire1]
  simp only [hadamard, Matrix.of_apply]
  by_cases hother : ∀ a : Fin n, a ≠ i → y a = q a
  · rw [if_pos hother]
    have hy_false : y = Function.update q i false ↔ y i = false := by
      constructor
      · intro h; simp [h]
      · intro h; funext a; by_cases ha : a = i
        · subst ha; simp [h]
        · simp [ha, hother a ha]
    have hy_true : y = Function.update q i true ↔ y i = true := by
      constructor
      · intro h; simp [h]
      · intro h; funext a; by_cases ha : a = i
        · subst ha; simp [h]
        · simp [ha, hother a ha]
    cases hyi : y i
    · have hf : y = Function.update q i false := hy_false.mpr hyi
      have ht : y ≠ Function.update q i true := fun h => by have := hy_true.mp h; simp_all
      rw [if_pos hf, if_neg ht]
      cases hqi : q i <;> simp
    · have hf : y ≠ Function.update q i false := fun h => by have := hy_false.mp h; simp_all
      have ht : y = Function.update q i true := hy_true.mpr hyi
      rw [if_neg hf, if_pos ht]
      cases hqi : q i <;> simp
  · rw [if_neg hother]
    have hne_f : y ≠ Function.update q i false := by
      intro h; apply hother; intro a hai; simp [h, hai]
    have hne_t : y ≠ Function.update q i true := by
      intro h; apply hother; intro a hai; simp [h, hai]
    rw [if_neg hne_f, if_neg hne_t]
    simp

lemma act_x_ket {n : ℕ} (i : Fin n) (q : Qubits n) :
    act (circUnitary [.x i]) (ket q) = ket (Function.update q i (!q i)) := by
  rw [instr_x_unitary, act_permMat]

lemma act_cnot_ket {n : ℕ} (i j : Fin n) (hij : i ≠ j) (q : Qubits n) :
    act (circUnitary [.cnot i j hij]) (ket q) =
      ket (Function.update q j (xor (q j) (q i))) := by
  rw [instr_cnot_unitary, act_permMat]

lemma act_s_ket {n : ℕ} (i : Fin n) (q : Qubits n) :
    act (circUnitary [.s i]) (ket q) = (if q i then Complex.I else 1) • ket q := by
  rw [instr_s_unitary, act_diagonal]

lemma act_t_ket {n : ℕ} (i : Fin n) (q : Qubits n) :
    act (circUnitary [.t i]) (ket q) =
      (if q i then Complex.exp (Complex.I * Real.pi / 4) else 1) • ket q := by
  rw [instr_t_unitary, act_diagonal]

def tdg {n : ℕ} (i : Fin n) : List (Instr n) := [.s i, .s i, .s i, .t i]

lemma act_tdg_ket {n : ℕ} (i : Fin n) (q : Qubits n) :
    act (circUnitary (tdg i)) (ket q) =
      (if q i then (-Complex.I) * Complex.exp (Complex.I * Real.pi / 4) else 1) • ket q := by
  have h : tdg i = [.s i] ++ [.s i] ++ [.s i] ++ [.t i] := rfl
  rw [h]
  simp only [circUnitary_append, act_mul, act_s_ket, act_t_ket, act_smul, smul_smul]
  cases q i
  · simp
  · simp only [↓reduceIte]
    congr 1
    calc Complex.I * Complex.I * Complex.I * Complex.exp (Complex.I * ↑Real.pi / 4)
        = (Complex.I * Complex.I) * Complex.I * Complex.exp (Complex.I * ↑Real.pi / 4) := by ring
      _ = (-1) * Complex.I * Complex.exp (Complex.I * ↑Real.pi / 4) := by rw [Complex.I_mul_I]
      _ = -Complex.I * Complex.exp (Complex.I * ↑Real.pi / 4) := by ring

lemma omega_sq :
    Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4) = Complex.I := by
  rw [← Complex.exp_add]
  have harg : Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4 = (Real.pi / 2 : ℂ) * Complex.I := by ring
  rw [harg, Complex.exp_pi_div_two_mul_I]

lemma sqrt2_inv_sq : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = (2 : ℂ)⁻¹ := by
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hr
  simpa using hc

def q3 (a b c : Bool) : Qubits 3
  | 0 => a
  | 1 => b
  | 2 => c

@[simp] lemma q3_0 (a b c : Bool) : q3 a b c 0 = a := rfl
@[simp] lemma q3_1 (a b c : Bool) : q3 a b c 1 = b := rfl
@[simp] lemma q3_2 (a b c : Bool) : q3 a b c 2 = c := rfl

lemma q3_eq_iff (q : Qubits 3) : q = q3 (q 0) (q 1) (q 2) := by
  ext i; fin_cases i <;> rfl

lemma update_q3_2 (a b c x : Bool) : Function.update (q3 a b c) 2 x = q3 a b x := by
  ext i; fin_cases i <;> rfl

lemma update_q3_1 (a b c x : Bool) : Function.update (q3 a b c) 1 x = q3 a x c := by
  ext i; fin_cases i <;> rfl

def ket3 (a b : Bool) (α β : ℂ) : EuclideanSpace ℂ (Qubits 3) :=
  α • ket (q3 a b false) + β • ket (q3 a b true)

lemma ket3_h2 (a b : Bool) (α β : ℂ) :
    act (circUnitary [.h 2]) (ket3 a b α β) =
      ket3 a b (((Real.sqrt 2)⁻¹ : ℂ) * (α + β)) (((Real.sqrt 2)⁻¹ : ℂ) * (α - β)) := by
  simp only [ket3, act_add, act_smul, act_h_ket, q3_2, update_q3_2]
  simp only [Bool.false_eq_true, ↓reduceIte, one_smul, smul_add, smul_smul]
  rw [add_add_add_comm]
  congr 1
  · rw [← add_smul]; congr 1; ring
  · rw [← add_smul]; congr 1; ring

lemma ket3_cnot12 (a b : Bool) (α β : ℂ) :
    act (circUnitary [.cnot 1 2 (by decide)]) (ket3 a b α β) =
      if b then ket3 a b β α else ket3 a b α β := by
  simp only [ket3, act_add, act_smul, act_cnot_ket, q3_1, q3_2, update_q3_2]
  cases b <;> simp [add_comm]

lemma ket3_cnot02 (a b : Bool) (α β : ℂ) :
    act (circUnitary [.cnot 0 2 (by decide)]) (ket3 a b α β) =
      if a then ket3 a b β α else ket3 a b α β := by
  simp only [ket3, act_add, act_smul, act_cnot_ket, q3_0, q3_2, update_q3_2]
  cases a <;> simp [add_comm]

lemma ket3_t2 (a b : Bool) (α β : ℂ) :
    act (circUnitary [.t 2]) (ket3 a b α β) =
      ket3 a b α (Complex.exp (Complex.I * Real.pi / 4) * β) := by
  simp only [ket3, act_add, act_smul, act_t_ket, q3_2, Bool.false_eq_true, ↓reduceIte,
    one_smul, smul_smul]
  rw [mul_comm β _]

lemma ket3_tdg2 (a b : Bool) (α β : ℂ) :
    act (circUnitary (tdg 2)) (ket3 a b α β) =
      ket3 a b α ((-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * β) := by
  simp only [ket3, act_add, act_smul, act_tdg_ket, q3_2, Bool.false_eq_true, ↓reduceIte,
    one_smul, smul_smul]
  rw [mul_comm β _]

def ccx3Mid : List (Instr 3) :=
  [.h 2, .cnot 1 2 (by decide)] ++ tdg 2 ++
  [.cnot 0 2 (by decide), .t 2, .cnot 1 2 (by decide)] ++ tdg 2 ++
  [.cnot 0 2 (by decide), .t 2, .h 2]

def ccx3 : List (Instr 3) :=
  ccx3Mid ++ [.t 1, .cnot 0 1 (by decide), .t 0] ++ tdg 1 ++ [.cnot 0 1 (by decide)]

lemma act_ccx3Mid_ket (a b c : Bool) :
    act (circUnitary ccx3Mid) (ket (q3 a b c)) =
      (if a && b then -Complex.I else 1) • ket (q3 a b (xor c (a && b))) := by
  set s : ℂ := ((Real.sqrt 2)⁻¹ : ℂ)
  have hs2 : s * s = (2 : ℂ)⁻¹ := sqrt2_inv_sq
  have hω2 : ∀ z : ℂ, Complex.exp (Complex.I * Real.pi / 4) * (Complex.exp (Complex.I * Real.pi / 4) * z) = Complex.I * z := by
    intro z; rw [← mul_assoc, omega_sq]
  have hωω' : ∀ z : ℂ, Complex.exp (Complex.I * Real.pi / 4) * ((-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * z) = z := by
    intro z
    calc Complex.exp (Complex.I * Real.pi / 4) * ((-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * z)
        = (-Complex.I * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4))) * z := by ring
      _ = (-Complex.I * Complex.I) * z := by rw [omega_sq]
      _ = z := by simp [Complex.I_mul_I]
  have hω'ω : ∀ z : ℂ, (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * (Complex.exp (Complex.I * Real.pi / 4) * z) = z := by
    intro z
    calc (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * (Complex.exp (Complex.I * Real.pi / 4) * z)
        = (-Complex.I * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4))) * z := by ring
      _ = (-Complex.I * Complex.I) * z := by rw [omega_sq]
      _ = z := by simp [Complex.I_mul_I]
  have hω'2 : ∀ z : ℂ, (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * ((-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * z) = -Complex.I * z := by
    intro z
    calc (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * ((-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * z)
        = ((Complex.I * Complex.I) * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4))) * z := by ring
      _ = ((-1) * Complex.I) * z := by rw [Complex.I_mul_I, omega_sq]
      _ = -Complex.I * z := by ring
  have hsplit : ccx3Mid =
      [.h 2] ++ [.cnot 1 2 (by decide)] ++ tdg 2 ++ [.cnot 0 2 (by decide)] ++
      [.t 2] ++ [.cnot 1 2 (by decide)] ++ tdg 2 ++ [.cnot 0 2 (by decide)] ++
      [.t 2] ++ [.h 2] := by
    simp [ccx3Mid, List.append_assoc]
  set α₀ : ℂ := if c then 0 else 1
  set β₀ : ℂ := if c then 1 else 0
  have hket : ket (q3 a b c) = ket3 a b α₀ β₀ := by
    cases c <;> simp [ket3, α₀, β₀]
  rw [hsplit, hket]
  simp only [circUnitary_append, act_mul]
  change act (circUnitary [.h 2]) (act (circUnitary [.t 2]) (act (circUnitary [.cnot 0 2 (by decide)])
    (act (circUnitary (tdg 2)) (act (circUnitary [.cnot 1 2 (by decide)]) (act (circUnitary [.t 2])
      (act (circUnitary [.cnot 0 2 (by decide)]) (act (circUnitary (tdg 2))
        (act (circUnitary [.cnot 1 2 (by decide)]) (act (circUnitary [.h 2])
          (ket3 a b α₀ β₀)))))))))) = _
  rw [ket3_h2, ket3_cnot12]
  cases b
  · rw [if_neg Bool.false_ne_true, ket3_tdg2, ket3_cnot02]
    cases a
    · rw [if_neg Bool.false_ne_true, ket3_t2, hωω',
        ket3_cnot12, if_neg Bool.false_ne_true, ket3_tdg2, ket3_cnot02,
        if_neg Bool.false_ne_true, ket3_t2, hωω', ket3_h2]
      have h1 : s * (s * (α₀ + β₀) + s * (α₀ - β₀)) = α₀ := by
        calc s * (s * (α₀ + β₀) + s * (α₀ - β₀)) = (s * s) * (2 * α₀) := by ring
          _ = (2 : ℂ)⁻¹ * (2 * α₀) := by rw [hs2]
          _ = α₀ := by ring
      have h2 : s * (s * (α₀ + β₀) - s * (α₀ - β₀)) = β₀ := by
        calc s * (s * (α₀ + β₀) - s * (α₀ - β₀)) = (s * s) * (2 * β₀) := by ring
          _ = (2 : ℂ)⁻¹ * (2 * β₀) := by rw [hs2]
          _ = β₀ := by ring
      change ket3 false false (s * (s * (α₀ + β₀) + s * (α₀ - β₀))) (s * (s * (α₀ + β₀) - s * (α₀ - β₀))) = _
      rw [h1, h2, ← hket]; simp
    · rw [if_pos rfl, ket3_t2, ket3_cnot12, if_neg Bool.false_ne_true,
        ket3_tdg2, hω'ω, ket3_cnot02, if_pos rfl,
        ket3_t2, hωω', ket3_h2]
      have h1 : s * (s * (α₀ + β₀) + s * (α₀ - β₀)) = α₀ := by
        calc s * (s * (α₀ + β₀) + s * (α₀ - β₀)) = (s * s) * (2 * α₀) := by ring
          _ = (2 : ℂ)⁻¹ * (2 * α₀) := by rw [hs2]
          _ = α₀ := by ring
      have h2 : s * (s * (α₀ + β₀) - s * (α₀ - β₀)) = β₀ := by
        calc s * (s * (α₀ + β₀) - s * (α₀ - β₀)) = (s * s) * (2 * β₀) := by ring
          _ = (2 : ℂ)⁻¹ * (2 * β₀) := by rw [hs2]
          _ = β₀ := by ring
      change ket3 true false (s * (s * (α₀ + β₀) + s * (α₀ - β₀))) (s * (s * (α₀ + β₀) - s * (α₀ - β₀))) = _
      rw [h1, h2, ← hket]; simp
  · rw [if_pos rfl, ket3_tdg2, ket3_cnot02]
    cases a
    · rw [if_neg Bool.false_ne_true, ket3_t2, hωω',
        ket3_cnot12, if_pos rfl, ket3_tdg2, ket3_cnot02, if_neg Bool.false_ne_true,
        ket3_t2, hωω', ket3_h2]
      have h1 : s * (s * (α₀ + β₀) + s * (α₀ - β₀)) = α₀ := by
        calc s * (s * (α₀ + β₀) + s * (α₀ - β₀)) = (s * s) * (2 * α₀) := by ring
          _ = (2 : ℂ)⁻¹ * (2 * α₀) := by rw [hs2]
          _ = α₀ := by ring
      have h2 : s * (s * (α₀ + β₀) - s * (α₀ - β₀)) = β₀ := by
        calc s * (s * (α₀ + β₀) - s * (α₀ - β₀)) = (s * s) * (2 * β₀) := by ring
          _ = (2 : ℂ)⁻¹ * (2 * β₀) := by rw [hs2]
          _ = β₀ := by ring
      change ket3 false true (s * (s * (α₀ + β₀) + s * (α₀ - β₀))) (s * (s * (α₀ + β₀) - s * (α₀ - β₀))) = _
      rw [h1, h2, ← hket]; simp
    · rw [if_pos rfl, ket3_t2, ket3_cnot12, if_pos rfl,
        ket3_tdg2, hω'2, ket3_cnot02, if_pos rfl,
        ket3_t2, hω2, ket3_h2]
      have h1 : s * (-Complex.I * (s * (α₀ + β₀)) + Complex.I * (s * (α₀ - β₀))) = -Complex.I * β₀ := by
        calc s * (-Complex.I * (s * (α₀ + β₀)) + Complex.I * (s * (α₀ - β₀)))
            = (s * s) * (-2 * Complex.I * β₀) := by ring
          _ = (2 : ℂ)⁻¹ * (-2 * Complex.I * β₀) := by rw [hs2]
          _ = -Complex.I * β₀ := by ring
      have h2 : s * (-Complex.I * (s * (α₀ + β₀)) - Complex.I * (s * (α₀ - β₀))) = -Complex.I * α₀ := by
        calc s * (-Complex.I * (s * (α₀ + β₀)) - Complex.I * (s * (α₀ - β₀)))
            = (s * s) * (-2 * Complex.I * α₀) := by ring
          _ = (2 : ℂ)⁻¹ * (-2 * Complex.I * α₀) := by rw [hs2]
          _ = -Complex.I * α₀ := by ring
      change ket3 true true (s * (-Complex.I * (s * (α₀ + β₀)) + Complex.I * (s * (α₀ - β₀))))
        (s * (-Complex.I * (s * (α₀ + β₀)) - Complex.I * (s * (α₀ - β₀)))) = _
      rw [h1, h2]
      cases c <;> simp [ket3, α₀, β₀]

lemma act_ccx3_ket (q : Qubits 3) :
    act (circUnitary ccx3) (ket q) =
      ket (Function.update q 2 (xor (q 2) (q 0 && q 1))) := by
  rw [q3_eq_iff q]
  change act (circUnitary ccx3) (ket (q3 (q 0) (q 1) (q 2))) =
      ket (Function.update (q3 (q 0) (q 1) (q 2)) 2 (xor (q 2) (q 0 && q 1)))
  rw [update_q3_2]
  have hsplit : ccx3 =
      ccx3Mid ++ [.t 1] ++ [.cnot 0 1 (by decide)] ++ [.t 0] ++ tdg 1 ++ [.cnot 0 1 (by decide)] := by
    simp [ccx3, List.append_assoc]
  rw [hsplit]
  simp only [circUnitary_append, act_mul, act_ccx3Mid_ket]
  change act (circUnitary [.cnot 0 1 (by decide)]) (act (circUnitary (tdg 1))
    (act (circUnitary [.t 0]) (act (circUnitary [.cnot 0 1 (by decide)])
      (act (circUnitary [.t 1]) ((if q 0 && q 1 then -Complex.I else 1) •
        ket (q3 (q 0) (q 1) (xor (q 2) (q 0 && q 1)))))))) = _
  cases h0 : q 0 <;> cases h1 : q 1
  · simp only [act_t_ket, act_cnot_ket, act_tdg_ket, q3_0, q3_1,
      update_q3_1, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      Bool.xor_false, one_smul]
  · simp only [act_smul, act_t_ket, act_cnot_ket, act_tdg_ket, q3_0, q3_1,
      update_q3_1, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      Bool.xor_false, one_smul, smul_smul]
    rw [show Complex.exp (Complex.I * Real.pi / 4) * (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) = 1 by
      calc Complex.exp (Complex.I * Real.pi / 4) * (-Complex.I * Complex.exp (Complex.I * Real.pi / 4))
          = -Complex.I * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4)) := by ring
        _ = -Complex.I * Complex.I := by rw [omega_sq]
        _ = 1 := by simp [Complex.I_mul_I]]
    simp [one_smul]
  · simp only [act_smul, act_t_ket, act_cnot_ket, act_tdg_ket, q3_0, q3_1,
      update_q3_1, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true, one_smul, smul_smul]
    rw [show Complex.exp (Complex.I * Real.pi / 4) * (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) = 1 by
      calc Complex.exp (Complex.I * Real.pi / 4) * (-Complex.I * Complex.exp (Complex.I * Real.pi / 4))
          = -Complex.I * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4)) := by ring
        _ = -Complex.I * Complex.I := by rw [omega_sq]
        _ = 1 := by simp [Complex.I_mul_I]]
    simp [one_smul]
  · simp only [act_smul, act_t_ket, act_cnot_ket, act_tdg_ket, q3_0, q3_1,
      update_q3_1, Bool.true_and, ↓reduceIte, Bool.xor_true, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, smul_smul, mul_one]
    rw [show (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * Complex.exp (Complex.I * Real.pi / 4) = 1 by
      calc (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * Complex.exp (Complex.I * Real.pi / 4)
          = -Complex.I * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4)) := by ring
        _ = -Complex.I * Complex.I := by rw [omega_sq]
        _ = 1 := by simp [Complex.I_mul_I]]
    simp [one_smul]

lemma circUnitary_ccx3 :
    circUnitary ccx3 =
      permMat (fun q : Qubits 3 => Function.update q 2 (xor (q 2) (q 0 && q 1))) := by
  apply matrix_eq_of_act_ket
  intro q
  rw [act_ccx3_ket, act_permMat]

/-! ### Section 2: `embedOp` composition and `RevGate` macro-instructions -/

lemma embedOp_mul {k n : ℕ} (A B : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    let agree (u : Qubits n) : Prop := ∀ a : Fin n, a ∉ Set.range w → y a = u a
    let mkU (v : Qubits k) : Qubits n := fun a => if h : ∃ i, w i = a then v h.choose else y a
    have hmkU_w : ∀ v i, mkU v (w i) = v i := by
      intro v i
      have hex : ∃ j, w j = w i := ⟨i, rfl⟩
      simp only [mkU, dif_pos hex]
      congr 1
      exact w.injective hex.choose_spec
    have hmkU_off : ∀ v, agree (mkU v) := by
      intro v a ha
      have hneg : ¬ ∃ i, w i = a := by simpa [Set.mem_range] using ha
      simp only [mkU, dif_neg hneg]
    have hmkU_id : ∀ u, agree u → mkU (fun i => u (w i)) = u := by
      intro u hu
      funext a
      by_cases hex : ∃ i, w i = a
      · rcases hex with ⟨i, rfl⟩
        exact hmkU_w (fun i => u (w i)) i
      · simp only [mkU, dif_neg hex]
        exact hu a (fun ⟨i, hi⟩ => hex ⟨i, hi⟩)
    have hsum1 : (∑ u : Qubits n,
          (if agree u then A (y ∘ w) (u ∘ w) else 0) *
          (if ∀ a, a ∉ Set.range w → u a = z a then B (u ∘ w) (z ∘ w) else 0)) =
        ∑ u ∈ Finset.univ.filter agree, A (y ∘ w) (u ∘ w) * B (u ∘ w) (z ∘ w) := by
      have hrew : (∑ u : Qubits n,
            (if agree u then A (y ∘ w) (u ∘ w) else 0) *
            (if ∀ a, a ∉ Set.range w → u a = z a then B (u ∘ w) (z ∘ w) else 0)) =
          ∑ u : Qubits n, if agree u then A (y ∘ w) (u ∘ w) * B (u ∘ w) (z ∘ w) else 0 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hua : agree u
        · have huz : ∀ a, a ∉ Set.range w → u a = z a := fun a ha => (hua a ha).symm.trans (hyz a ha)
          rw [if_pos hua, if_pos huz, if_pos hua]
        · rw [if_neg hua, zero_mul, if_neg hua]
      rw [hrew, ← Finset.sum_filter]
    rw [hsum1]
    refine Finset.sum_nbij' mkU (fun (u : Qubits n) (i : Fin k) => u (w i)) ?_ ?_ ?_ ?_ ?_
    · intro v _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmkU_off v⟩
    · intro u _; exact Finset.mem_univ _
    · intro v _; funext i; exact hmkU_w v i
    · intro u hu; exact hmkU_id u (Finset.mem_filter.mp hu).2
    · intro v _
      have hcomp : mkU v ∘ w = v := by funext i; exact hmkU_w v i
      rw [hcomp]
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero fun u _ => ?_
    split_ifs with h1 h2
    · exfalso; exact hyz fun a ha => (h1 a ha).trans (h2 a ha)
    · simp
    · simp
    · simp

lemma embedOp_trans {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin m) (e : Fin m ↪ Fin n) :
    embedOp (embedOp M w) e = embedOp M (w.trans e) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  have hiff : ((∀ a : Fin n, a ∉ Set.range e → y a = z a) ∧
      (∀ b : Fin m, b ∉ Set.range w → y (e b) = z (e b))) ↔
      (∀ a : Fin n, a ∉ Set.range (w.trans e) → y a = z a) := by
    constructor
    · rintro ⟨h1, h2⟩ a ha
      by_cases hae : a ∈ Set.range e
      · rcases hae with ⟨b, rfl⟩
        exact h2 b fun ⟨i, hi⟩ => ha ⟨i, by simp [hi]⟩
      · exact h1 a hae
    · intro h
      refine ⟨fun a ha => h a fun ⟨i, hi⟩ => ha ⟨w i, by simpa using hi⟩, ?_⟩
      intro b hb
      apply h (e b)
      rintro ⟨i, hi⟩
      exact hb ⟨i, e.injective hi⟩
  have hc1 : (y ∘ e) ∘ w = y ∘ ⇑(w.trans e) := rfl
  have hc2 : (z ∘ e) ∘ w = z ∘ ⇑(w.trans e) := rfl
  by_cases h1 : ∀ a : Fin n, a ∉ Set.range e → y a = z a
  · by_cases h2 : ∀ b : Fin m, b ∉ Set.range w → (y ∘ e) b = (z ∘ e) b
    · have h3 : ∀ a : Fin n, a ∉ Set.range (w.trans e) → y a = z a := hiff.mp ⟨h1, h2⟩
      rw [if_pos h1, if_pos h2, if_pos h3, hc1, hc2]
    · have h3 : ¬ (∀ a : Fin n, a ∉ Set.range (w.trans e) → y a = z a) :=
        fun h => h2 (hiff.mpr h).2
      rw [if_pos h1, if_neg h2, if_neg h3]
  · have h3 : ¬ (∀ a : Fin n, a ∉ Set.range (w.trans e) → y a = z a) :=
      fun h => h1 (hiff.mpr h).1
    rw [if_neg h1, if_neg h3]

lemma instrApp_mapInstr {m n : ℕ} (e : Fin m ↪ Fin n) (ins : Instr m) :
    embedOp (instrApp (mapInstr e ins)).gate.mat (instrApp (mapInstr e ins)).wires =
      embedOp (instrApp ins).gate.mat ((instrApp ins).wires.trans e) := by
  cases ins with
  | h i | s i | t i | x i =>
    simp only [mapInstr, instrApp]
    congr 1
  | cnot i j hij =>
    simp only [mapInstr, instrApp]
    congr 1
    ext a
    fin_cases a <;> rfl

lemma circUnitary_mapCirc {m n : ℕ} (e : Fin m ↪ Fin n) (c : List (Instr m)) :
    circUnitary (mapCirc e c) = embedOp (circUnitary c) e := by
  induction c with
  | nil => simp [mapCirc, circUnitary_nil, embedOp_one]
  | cons g c ih =>
    have hc1 : mapCirc e (g :: c) = [mapInstr e g] ++ mapCirc e c := rfl
    have hc2 : g :: c = [g] ++ c := rfl
    rw [hc1, hc2, circUnitary_append, circUnitary_append, ih, embedOp_mul]
    congr 1
    simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
    rw [instrApp_mapInstr, ← embedOp_trans]

def wire3 {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Fin 3 ↪ Fin n :=
  ⟨![i, j, k], fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all [eq_comm]⟩

@[simp] lemma wire3_0 {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    wire3 i j k hij hik hjk 0 = i := rfl
@[simp] lemma wire3_1 {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    wire3 i j k hij hik hjk 1 = j := rfl
@[simp] lemma wire3_2 {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    wire3 i j k hij hik hjk 2 = k := rfl

lemma embedOp_wire3_ccx {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    embedOp (permMat (fun q : Qubits 3 => Function.update q 2 (xor (q 2) (q 0 && q 1))))
        (wire3 i j k hij hik hjk) =
      permMat (fun q : Qubits n => Function.update q k (xor (q k) (q i && q j))) := by
  let e := wire3 i j k hij hik hjk
  ext y z
  simp only [embedOp, permMat, Matrix.of_apply]
  by_cases hy : y = Function.update z k (xor (z k) (z i && z j))
  · subst hy
    rw [if_pos rfl, if_pos]
    · rw [if_pos]
      ext a
      fin_cases a
      · simp [hik]
      · simp [hjk]
      · simp
    · intro a ha
      have hak : a ≠ k := fun heq => ha ⟨2, by simp [heq]⟩
      simp [hak]
  · rw [if_neg hy]
    by_cases h1 : ∀ a : Fin n, a ∉ Set.range e → y a = z a
    · rw [if_pos h1]
      by_cases h2 : y ∘ e = Function.update (z ∘ e) 2 (xor ((z ∘ e) 2) ((z ∘ e) 0 && (z ∘ e) 1))
      · exfalso
        apply hy
        funext a
        by_cases hak : a = k
        · subst hak
          have h22 := congrFun h2 2
          simpa [e, wire3_0, wire3_1, wire3_2] using h22
        · by_cases hai : a = i
          · subst hai
            have h20 := congrFun h2 0
            simpa [e, wire3_0, hak] using h20
          · by_cases haj : a = j
            · subst haj
              have h21 := congrFun h2 1
              simpa [e, wire3_1, hak] using h21
            · have ha_range : a ∉ Set.range e := by
                rintro ⟨b, hb⟩
                fin_cases b
                · exact hai (by simpa [e, wire3_0] using hb.symm)
                · exact haj (by simpa [e, wire3_1] using hb.symm)
                · exact hak (by simpa [e, wire3_2] using hb.symm)
              simpa [hak] using h1 a ha_range
      · rw [if_neg h2]
    · rw [if_neg h1]

inductive RevGate (n : ℕ) where
  | x (i : Fin n)
  | cnot (i j : Fin n) (hij : i ≠ j)
  | ccx (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)

def RevGate.eval {n : ℕ} : RevGate n → Qubits n → Qubits n
  | .x i, q => Function.update q i (!q i)
  | .cnot i j _, q => Function.update q j (xor (q j) (q i))
  | .ccx i j k _ _ _, q => Function.update q k (xor (q k) (q i && q j))

lemma RevGate.eval_involutive {n : ℕ} (g : RevGate n) (q : Qubits n) :
    g.eval (g.eval q) = q := by
  cases g with
  | x i =>
    funext a; by_cases ha : a = i
    · subst ha; simp [RevGate.eval]
    · simp [RevGate.eval, ha]
  | cnot i j hij =>
    funext a; by_cases ha : a = j
    · subst ha; simp [RevGate.eval, hij]
    · simp [RevGate.eval, ha]
  | ccx i j k hij hik hjk =>
    funext a; by_cases ha : a = k
    · subst ha; simp [RevGate.eval, hik, hjk]
    · simp [RevGate.eval, ha]

def evalRev {n : ℕ} (gs : List (RevGate n)) (q : Qubits n) : Qubits n :=
  gs.foldl (fun s g => g.eval s) q

lemma evalRev_nil {n : ℕ} (q : Qubits n) : evalRev [] q = q := rfl

lemma evalRev_cons {n : ℕ} (g : RevGate n) (gs : List (RevGate n)) (q : Qubits n) :
    evalRev (g :: gs) q = evalRev gs (g.eval q) := rfl

lemma evalRev_append {n : ℕ} (gs₁ gs₂ : List (RevGate n)) (q : Qubits n) :
    evalRev (gs₁ ++ gs₂) q = evalRev gs₂ (evalRev gs₁ q) := by
  simp [evalRev, List.foldl_append]

lemma evalRev_reverse {n : ℕ} (gs : List (RevGate n)) (q : Qubits n) :
    evalRev gs.reverse (evalRev gs q) = q := by
  induction gs generalizing q with
  | nil => rfl
  | cons g gs ih =>
    rw [List.reverse_cons, evalRev_cons, evalRev_append, ih, evalRev_cons, evalRev_nil,
      RevGate.eval_involutive]

def RevGate.compile {n : ℕ} : RevGate n → List (Instr n)
  | .x i => [.x i]
  | .cnot i j hij => [.cnot i j hij]
  | .ccx i j k hij hik hjk => mapCirc (wire3 i j k hij hik hjk) ccx3

def compileRev {n : ℕ} (gs : List (RevGate n)) : List (Instr n) :=
  gs.flatMap RevGate.compile

lemma compileRev_append {n : ℕ} (gs₁ gs₂ : List (RevGate n)) :
    compileRev (gs₁ ++ gs₂) = compileRev gs₁ ++ compileRev gs₂ := by
  simp [compileRev, List.flatMap_append]

lemma circUnitary_compile {n : ℕ} (g : RevGate n) :
    circUnitary g.compile = permMat g.eval := by
  cases g with
  | x i => exact instr_x_unitary i
  | cnot i j hij => exact instr_cnot_unitary i j hij
  | ccx i j k hij hik hjk =>
    simp only [RevGate.compile]
    rw [circUnitary_mapCirc, circUnitary_ccx3, embedOp_wire3_ccx]
    rfl

lemma circUnitary_compileRev {n : ℕ} (gs : List (RevGate n)) :
    circUnitary (compileRev gs) = permMat (evalRev gs) := by
  induction gs with
  | nil =>
    have hev : (evalRev ([] : List (RevGate n))) = id := rfl
    simp [compileRev, circUnitary_nil, hev, permMat_id]
  | cons g gs ih =>
    have hcomp : compileRev (g :: gs) = g.compile ++ compileRev gs := rfl
    rw [hcomp, circUnitary_append, ih, circUnitary_compile, permMat_mul]
    rfl

lemma compileRev_length_le {n : ℕ} (gs : List (RevGate n)) :
    (compileRev gs).length ≤ ccx3.length * gs.length := by
  induction gs with
  | nil => simp [compileRev]
  | cons g gs ih =>
    simp only [compileRev, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have hg : g.compile.length ≤ ccx3.length := by
      cases g with
      | x _ => simp [RevGate.compile, ccx3, ccx3Mid, tdg]
      | cnot _ _ _ => simp [RevGate.compile, ccx3, ccx3Mid, tdg]
      | ccx _ _ _ _ _ _ => simp [RevGate.compile, mapCirc]
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-! ### Section 3: Quantum `Implements` bridges and the `gamma_mark_phase_and_unmark` circuits -/

lemma embedVec_sum_ket {X : Type} [Fintype X] {n : ℕ} (code : X → Qubits n)
    (ψ : EuclideanSpace ℂ X) :
    embedVec code ψ = ∑ x : X, ψ x • ket (code x) := by
  have hsum : ∀ s : Finset X, ∀ f : X → EuclideanSpace ℂ (Qubits n), ∀ y : Qubits n,
      WithLp.ofLp (∑ x ∈ s, f x) y = ∑ x ∈ s, WithLp.ofLp (f x) y := by
    intro s f y
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih => simp [Finset.sum_insert ha, ih]
  apply WithLp.ofLp_injective
  funext y
  rw [hsum Finset.univ (fun x => ψ x • ket (code x)) y]
  simp only [embedVec, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul, ket_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : code x = y
  · subst h; simp
  · have h' : y ≠ code x := Ne.symm h
    simp [h, h']

lemma implements_of_act_ket_diagonal {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (U : Matrix (Qubits n) (Qubits n) ℂ) (cin cout : X → Qubits n) (d : X → ℂ)
    (hact : ∀ x : X, act U (ket (cin x)) = d x • ket (cout x)) (ε : ℝ) (hε : 0 ≤ ε) :
    Implements U cin cout (Matrix.diagonal d) ε := by
  intro ψ
  have hL : act U (embedVec cin ψ) =
      embedVec cout (WithLp.toLp 2 ((Matrix.diagonal d).mulVec (WithLp.ofLp ψ))) := by
    rw [embedVec_sum_ket, embedVec_sum_ket]
    have hact_sum : ∀ s : Finset X, ∀ f : X → EuclideanSpace ℂ (Qubits n),
        act U (∑ x ∈ s, f x) = ∑ x ∈ s, act U (f x) := by
      intro s f
      induction s using Finset.induction_on with
      | empty =>
        apply WithLp.ofLp_injective; funext y; simp [act]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, act_add, ih]
    rw [hact_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [act_smul, hact x, smul_smul]
    simp [Matrix.mulVec_diagonal, mul_comm]
  rw [hL, sub_self, norm_zero]
  exact mul_nonneg hε (norm_nonneg ψ)

lemma implements_of_act_ket_one {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (U : Matrix (Qubits n) (Qubits n) ℂ) (cin cout : X → Qubits n)
    (hact : ∀ x : X, act U (ket (cin x)) = ket (cout x)) (ε : ℝ) (hε : 0 ≤ ε) :
    Implements U cin cout 1 ε := by
  have h1 : (1 : Matrix X X ℂ) = Matrix.diagonal (fun _ => (1 : ℂ)) := by
    ext a b; simp [Matrix.one_apply, Matrix.diagonal_apply]
  rw [h1]
  exact implements_of_act_ket_diagonal U cin cout (fun _ => 1) (fun x => by simpa using hact x) ε hε

def gammaW (D : FieldData) : ℕ := 1 + (D.r + 1) * D.labW + D.labW

lemma two_le_labW (D : FieldData) : 2 ≤ D.labW := by
  unfold FieldData.labW
  have hq : 2 ≤ D.q := D.one_lt_q
  have h4 : 4 ≤ D.q ^ 2 := by nlinarith
  have hpow : 2 ^ 1 < D.q ^ 2 := by omega
  have hlt : 1 < Nat.clog 2 (D.q ^ 2) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr hpow
  omega

lemma two_mul_labW_le_tagW (D : FieldData) : 2 * D.labW ≤ (D.r + 1) * D.labW := by
  have hr : 1 ≤ D.r := D.hr
  nlinarith

lemma val_lt_two_pow_labW (D : FieldData) (α : D.Lab) : α.val < 2 ^ D.labW := by
  have h1 : α.val < D.q - 1 := ZMod.val_lt α
  have hq : 1 < D.q := D.one_lt_q
  have h2 : D.q ≤ D.q ^ 2 := Nat.le_self_pow (by decide) D.q
  have h3 : D.q ^ 2 ≤ 2 ^ D.labW := Nat.le_pow_clog (by decide) (D.q ^ 2)
  omega

lemma testBit_eq_false_iff_zero {n L : ℕ} (hn : n < 2 ^ L) :
    (∀ j < L, n.testBit j = false) ↔ n = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.zero_testBit]
    by_cases hj : j < L
    · exact h j hj
    · have hle : 2 ^ L ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.testBit_lt_two_pow (hn.trans_le hle)
  · rintro rfl j _; simp

def swapRev {n : ℕ} (a b : Fin n) (hab : a ≠ b) : List (RevGate n) :=
  [.cnot a b hab, .cnot b a hab.symm, .cnot a b hab]

lemma evalRev_swapRev {n : ℕ} (a b : Fin n) (hab : a ≠ b) (q : Qubits n) :
    evalRev (swapRev a b hab) q = Function.update (Function.update q a (q b)) b (q a) := by
  funext x
  simp only [swapRev, evalRev_cons, evalRev_nil, RevGate.eval]
  by_cases hxb : x = b
  · subst hxb; simp [hab, hab.symm]
  · by_cases hxa : x = a
    · subst hxa; simp [hab]; cases q x <;> cases q b <;> rfl
    · simp [hxa, hxb]

def shiftUpAux {W N : ℕ} (hWN : W < N) : (k : ℕ) → k ≤ W → List (RevGate N)
  | 0, _ => []
  | k + 1, hk =>
    let a : Fin N := ⟨k, by omega⟩
    let b : Fin N := ⟨k + 1, by omega⟩
    swapRev a b (by simp [Fin.ext_iff, a, b]) ++ shiftUpAux hWN k (by omega)

lemma evalRev_shiftUpAux {W N : ℕ} (hWN : W < N) (k : ℕ) (hk : k ≤ W) (q : Qubits N) :
    (evalRev (shiftUpAux hWN k hk) q ⟨0, by omega⟩ = q ⟨k, by omega⟩) ∧
    (∀ i (hi : i < k), evalRev (shiftUpAux hWN k hk) q ⟨i + 1, by omega⟩ = q ⟨i, by omega⟩) ∧
    (∀ j : Fin N, k < j.val → evalRev (shiftUpAux hWN k hk) q j = q j) := by
  induction k generalizing q with
  | zero =>
    refine ⟨rfl, fun i hi => by omega, fun j _ => rfl⟩
  | succ k ih =>
    simp only [shiftUpAux, evalRev_append]
    let a : Fin N := ⟨k, by omega⟩
    let b : Fin N := ⟨k + 1, by omega⟩
    have hab : a ≠ b := by simp [Fin.ext_iff, a, b]
    set q' := evalRev (swapRev a b hab) q
    have hq'a : q' ⟨k, by omega⟩ = q ⟨k + 1, by omega⟩ := by
      dsimp [q']; rw [evalRev_swapRev]; simp [a, b, hab]
    have hq'b : q' ⟨k + 1, by omega⟩ = q ⟨k, by omega⟩ := by
      dsimp [q']; rw [evalRev_swapRev]; simp [a, b]
    have hq'other : ∀ x : Fin N, x.val ≠ k → x.val ≠ k + 1 → q' x = q x := by
      intro x hx1 hx2
      dsimp [q']; rw [evalRev_swapRev]
      have hxa : x ≠ a := fun h => hx1 (congrArg Fin.val h)
      have hxb : x ≠ b := fun h => hx2 (congrArg Fin.val h)
      simp [hxa, hxb]
    have ihq := ih (by omega) q'
    refine ⟨?_, ?_, ?_⟩
    · exact ihq.1.trans hq'a
    · intro i hi
      by_cases hik : i < k
      · exact (ihq.2.1 i hik).trans (hq'other ⟨i, by omega⟩ (by dsimp; omega) (by dsimp; omega))
      · have hieq : i = k := by omega
        subst i
        have hgt : k < (⟨k + 1, by omega⟩ : Fin N).val := by simp
        exact (ihq.2.2 ⟨k + 1, by omega⟩ hgt).trans hq'b
    · intro j hj
      exact (ihq.2.2 j (by omega)).trans (hq'other j (by omega) (by omega))

lemma gammaW_gt_tagW (D : FieldData) : (D.r + 1) * D.labW < gammaW D := by
  unfold gammaW
  have := two_le_labW D
  omega

def shiftUp (D : FieldData) : List (RevGate (gammaW D)) :=
  shiftUpAux (gammaW_gt_tagW D) ((D.r + 1) * D.labW) le_rfl

lemma evalRev_shiftUp_tagCode (D : FieldData) (c : Option D.Lab) :
    evalRev (shiftUp D) (padTo (gammaW D) (D.tagCode (D.xEmb c))) =
      Function.update (padTo (gammaW D) (gammaTaggedCode D c)) ⟨0, by have := gammaW_gt_tagW D; omega⟩ false := by
  have hWN := gammaW_gt_tagW D
  have hres := evalRev_shiftUpAux hWN ((D.r + 1) * D.labW) le_rfl (padTo (gammaW D) (D.tagCode (D.xEmb c)))
  change evalRev (shiftUpAux hWN ((D.r + 1) * D.labW) le_rfl) _ = _
  funext j
  by_cases hj0 : j.val = 0
  · have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
    rw [hj_eq]
    have hWpad : padTo (gammaW D) (D.tagCode (D.xEmb c)) ⟨(D.r + 1) * D.labW, hWN⟩ = false := by
      simp [padTo]
    rw [hres.1, hWpad, Function.update_self]
  · have hne0 : j ≠ ⟨0, by omega⟩ := fun h => hj0 (congrArg Fin.val h)
    rw [Function.update_of_ne hne0]
    by_cases hjW : j.val ≤ (D.r + 1) * D.labW
    · have hj_pred : j.val - 1 < (D.r + 1) * D.labW := by omega
      have hj_eq : j = ⟨(j.val - 1) + 1, by omega⟩ := by ext; simp; omega
      rw [hj_eq, hres.2.1 (j.val - 1) hj_pred]
      have h1 : (j.val - 1) + 1 < 1 + (D.r + 1) * D.labW := by omega
      simp only [padTo, dif_pos hj_pred, dif_pos h1, gammaTaggedCode, boolAppCode, Fin.append]
      simp [Fin.addCases]
    · have hj_gt : (D.r + 1) * D.labW < j.val := by omega
      rw [hres.2.2 j hj_gt]
      have h1 : ¬ j.val < (D.r + 1) * D.labW := by omega
      have h2 : ¬ j.val < 1 + (D.r + 1) * D.labW := by omega
      simp [padTo, h1, h2]

def ctrlWire (D : FieldData) (j : ℕ) (hj : j < D.labW) : Fin (gammaW D) :=
  ⟨1 + D.labW + j, by have := two_mul_labW_le_tagW D; unfold gammaW; omega⟩

def ancWire (D : FieldData) (j : ℕ) (hj : j < D.labW) : Fin (gammaW D) :=
  ⟨1 + (D.r + 1) * D.labW + j, by unfold gammaW; omega⟩

def flagWire (D : FieldData) : Fin (gammaW D) :=
  ⟨1, by have := two_le_labW D; unfold gammaW; omega⟩

def flipCtrlAux (D : FieldData) : (k : ℕ) → k ≤ D.labW → List (RevGate (gammaW D))
  | 0, _ => []
  | k + 1, hk => flipCtrlAux D k (by omega) ++ [.x (ctrlWire D k hk)]

def cascadeAux (D : FieldData) : (k : ℕ) → k ≤ D.labW → List (RevGate (gammaW D))
  | 0, _ => []
  | 1, hk =>
    [.ccx (flagWire D) (ctrlWire D 0 hk) (ancWire D 0 hk)
      (by simp [Fin.ext_iff, flagWire, ctrlWire]; have := two_le_labW D; omega)
      (by simp [Fin.ext_iff, flagWire, ancWire]; have := two_mul_labW_le_tagW D; have := two_le_labW D; omega)
      (by simp [Fin.ext_iff, ctrlWire, ancWire]; have := two_mul_labW_le_tagW D; omega)]
  | k + 2, hk =>
    cascadeAux D (k + 1) (by omega) ++
      [.ccx (ancWire D k (by omega)) (ctrlWire D (k + 1) hk) (ancWire D (k + 1) hk)
        (by simp [Fin.ext_iff, ancWire, ctrlWire]; have := two_mul_labW_le_tagW D; omega)
        (by simp [Fin.ext_iff, ancWire])
        (by simp [Fin.ext_iff, ctrlWire, ancWire]; have := two_mul_labW_le_tagW D; omega)]

def prepZero (D : FieldData) : List (RevGate (gammaW D)) :=
  flipCtrlAux D D.labW le_rfl ++ cascadeAux D D.labW le_rfl

def RevGate.avoids {n : ℕ} (w : ℕ) : RevGate n → Prop
  | .x i => i.val ≠ w
  | .cnot i j _ => i.val ≠ w ∧ j.val ≠ w
  | .ccx i j k _ _ _ => i.val ≠ w ∧ j.val ≠ w ∧ k.val ≠ w

lemma RevGate.eval_not_touch0 {n : ℕ} (g : RevGate n)
    (h0 : g.avoids 0)
    (q : Qubits n) (z : Fin n) (hz : z.val = 0) (b : Bool) :
    g.eval (Function.update q z b) = Function.update (g.eval q) z b := by
  cases g with
  | x i =>
    have hiz : i ≠ z := fun h => h0 (by simp [h, hz])
    funext a; by_cases haz : a = z
    · subst haz; simp [RevGate.eval, hiz.symm]
    · by_cases hai : a = i <;> simp [RevGate.eval, haz, hai, hiz]
  | cnot i j hij =>
    have hiz : i ≠ z := fun h => h0.1 (by simp [h, hz])
    have hjz : j ≠ z := fun h => h0.2 (by simp [h, hz])
    funext a; by_cases haz : a = z
    · subst haz; simp [RevGate.eval, hjz.symm]
    · by_cases haj : a = j <;> simp [RevGate.eval, haz, haj, hiz, hjz]
  | ccx i j k hij hik hjk =>
    have hiz : i ≠ z := fun h => h0.1 (by simp [h, hz])
    have hjz : j ≠ z := fun h => h0.2.1 (by simp [h, hz])
    have hkz : k ≠ z := fun h => h0.2.2 (by simp [h, hz])
    funext a; by_cases haz : a = z
    · subst haz; simp [RevGate.eval, hkz.symm]
    · by_cases hak : a = k <;> simp [RevGate.eval, haz, hak, hiz, hjz, hkz]

lemma flipCtrlAux_not_touch0 (D : FieldData) (k : ℕ) (hk : k ≤ D.labW) :
    ∀ g ∈ flipCtrlAux D k hk, g.avoids 0 := by
  induction k with
  | zero => intro g hg; cases hg
  | succ k ih =>
    intro g hg
    simp only [flipCtrlAux, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ih (by omega) g hg
    · simp [RevGate.avoids, ctrlWire]

lemma cascadeAux_not_touch0 (D : FieldData) (k : ℕ) (hk : k ≤ D.labW) :
    ∀ g ∈ cascadeAux D k hk, g.avoids 0 := by
  induction k with
  | zero => intro g hg; cases hg
  | succ k ih =>
    cases k with
    | zero =>
      intro g hg
      simp only [cascadeAux, List.mem_singleton] at hg
      subst hg
      simp [RevGate.avoids, flagWire, ctrlWire, ancWire]
    | succ k =>
      intro g hg
      simp only [cascadeAux, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact ih (by omega) g hg
      · simp [RevGate.avoids, ancWire, ctrlWire]

lemma evalRev_not_touch0 {n : ℕ} (gs : List (RevGate n))
    (hgs : ∀ g ∈ gs, g.avoids 0)
    (q : Qubits n) (z : Fin n) (hz : z.val = 0) (b : Bool) :
    evalRev gs (Function.update q z b) = Function.update (evalRev gs q) z b := by
  induction gs generalizing q with
  | nil => rfl
  | cons g gs ih =>
    rw [evalRev_cons, evalRev_cons, RevGate.eval_not_touch0 g (hgs g (List.mem_cons_self)) q z hz b]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (g.eval q)

lemma evalRev_flipCtrlAux (D : FieldData) (k : ℕ) (hk : k ≤ D.labW) (q : Qubits (gammaW D)) :
    (∀ j (hj : j < k), evalRev (flipCtrlAux D k hk) q (ctrlWire D j (by omega)) = !q (ctrlWire D j (by omega))) ∧
    (∀ x : Fin (gammaW D), (∀ j (hj : j < k), x ≠ ctrlWire D j (by omega)) →
      evalRev (flipCtrlAux D k hk) q x = q x) := by
  induction k generalizing q with
  | zero => exact ⟨fun j hj => by omega, fun x _ => rfl⟩
  | succ k ih =>
    simp only [flipCtrlAux, evalRev_append, evalRev_cons, evalRev_nil, RevGate.eval]
    have ihq := ih (by omega) q
    refine ⟨fun j hj => ?_, fun x hx => ?_⟩
    · by_cases hjk : j < k
      · have hne : ctrlWire D j (by omega) ≠ ctrlWire D k hk := by
          simp [Fin.ext_iff, ctrlWire]; omega
        rw [Function.update_of_ne hne, ihq.1 j hjk]
      · have hj_eq : j = k := by omega
        subst hj_eq
        rw [Function.update_self, ihq.2 (ctrlWire D j hk) (fun m hm => by simp [Fin.ext_iff, ctrlWire]; omega)]
    · have hxk : x ≠ ctrlWire D k hk := hx k (Nat.lt_succ_self k)
      rw [Function.update_of_ne hxk]
      exact ihq.2 x (fun m hm => hx m (Nat.lt_succ_of_lt hm))

lemma evalRev_cascadeAux (D : FieldData) (k : ℕ) (hk : k ≤ D.labW) (q : Qubits (gammaW D))
    (hanc : ∀ j (hj : j < k), q (ancWire D j (by omega)) = false) :
    (∀ j (hj : j < k),
      evalRev (cascadeAux D k hk) q (ancWire D j (by omega)) =
        (q (flagWire D) && (List.range (j + 1)).all (fun m => if hm : m < D.labW then q (ctrlWire D m hm) else false))) ∧
    (∀ x : Fin (gammaW D), (∀ j (hj : j < k), x ≠ ancWire D j (by omega)) →
      evalRev (cascadeAux D k hk) q x = q x) := by
  induction k generalizing q with
  | zero => exact ⟨fun j hj => by omega, fun x _ => rfl⟩
  | succ k ih =>
    cases k with
    | zero =>
      simp only [cascadeAux, evalRev_cons, evalRev_nil, RevGate.eval]
      refine ⟨fun j hj => ?_, fun x hx => ?_⟩
      · have hj0 : j = 0 := by omega
        subst hj0
        have h0 : 0 < D.labW := by omega
        rw [Function.update_self, hanc 0 (by omega), Bool.false_xor]
        simp [List.range_succ, h0]
      · have hx0 : x ≠ ancWire D 0 hk := hx 0 (by omega)
        rw [Function.update_of_ne hx0]
    | succ k =>
      simp only [cascadeAux, evalRev_append]
      have ihq := ih (by omega) q (fun j hj => hanc j (by omega))
      set q' := evalRev (cascadeAux D (k + 1) (by omega)) q
      have hne_prev : ancWire D k (by omega) ≠ ancWire D (k + 1) hk := by
        simp [Fin.ext_iff, ancWire]
      have hne_ctrl : ctrlWire D (k + 1) hk ≠ ancWire D (k + 1) hk := by
        simp [Fin.ext_iff, ctrlWire, ancWire]; have := two_mul_labW_le_tagW D; omega
      have hq'k : q' (ancWire D k (by omega)) =
          (q (flagWire D) && (List.range (k + 1)).all (fun m => if hm : m < D.labW then q (ctrlWire D m hm) else false)) :=
        ihq.1 k (Nat.lt_succ_self k)
      have hq'ctrl : q' (ctrlWire D (k + 1) hk) = q (ctrlWire D (k + 1) hk) :=
        ihq.2 (ctrlWire D (k + 1) hk) (fun j _ => by simp [Fin.ext_iff, ctrlWire, ancWire]; have := two_mul_labW_le_tagW D; omega)
      have hq'anc : q' (ancWire D (k + 1) hk) = false :=
        (ihq.2 (ancWire D (k + 1) hk) (fun j hj => by simp [Fin.ext_iff, ancWire]; omega)).trans
          (hanc (k + 1) (Nat.lt_succ_self _))
      refine ⟨fun j hj => ?_, fun x hx => ?_⟩
      · simp only [evalRev_cons, evalRev_nil, RevGate.eval]
        change Function.update q' _ _ _ = _
        by_cases hjk : j < k + 1
        · have hjne : ancWire D j (by omega) ≠ ancWire D (k + 1) hk := by
            simp [Fin.ext_iff, ancWire]; omega
          rw [Function.update_of_ne hjne]
          exact ihq.1 j hjk
        · have hj_eq : j = k + 1 := by omega
          subst hj_eq
          have hkl : k + 1 < D.labW := by omega
          rw [Function.update_self, hq'anc, Bool.false_xor, hq'k, hq'ctrl]
          simp [List.range_succ, hkl, Bool.and_assoc]
      · simp only [evalRev_cons, evalRev_nil, RevGate.eval]
        have hxk : x ≠ ancWire D (k + 1) hk := hx (k + 1) (Nat.lt_succ_self _)
        rw [Function.update_of_ne hxk]
        exact ihq.2 x (fun j hj => hx j (Nat.lt_succ_of_lt hj))

lemma tagCode_xEmb_zero_bit (D : FieldData) (c : Option D.Lab) :
    D.tagCode (D.xEmb c) ⟨0, by have := two_le_labW D; have := D.hr; positivity⟩ = c.isSome := by
  have hL : 0 < D.labW := by have := two_le_labW D; omega
  cases c with
  | none =>
    simp [FieldData.xEmb, FieldData.tagCode, packNat]
  | some α =>
    simp only [FieldData.xEmb, FieldData.tagCode, packNat, Option.isSome_some]
    have hdiv : 0 / D.labW = 0 := Nat.zero_div _
    have hmod : 0 % D.labW = 0 := Nat.zero_mod _
    simp [hdiv, hmod]

lemma tagCode_xEmb_lab_bit (D : FieldData) (α : D.Lab) (j : ℕ) (hj : j < D.labW) :
    D.tagCode (D.xEmb (some α)) ⟨D.labW + j, by have := two_mul_labW_le_tagW D; omega⟩ =
      α.val.testBit j := by
  simp only [FieldData.xEmb, FieldData.tagCode, packNat]
  have hL : 0 < D.labW := by have := two_le_labW D; omega
  have hdiv : (D.labW + j) / D.labW = 1 := by
    rw [Nat.add_div_left j hL, Nat.div_eq_of_lt hj]
  have hmod : (D.labW + j) % D.labW = j := by
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hj]
  simp [hdiv, hmod]

lemma evalRev_prepZero_ancLast (D : FieldData) (c : Option D.Lab) (b0 : Bool)
    (h0 : 0 < gammaW D) (hL : D.labW - 1 < D.labW) :
    evalRev (prepZero D) (Function.update (padTo (gammaW D) (gammaTaggedCode D c)) ⟨0, h0⟩ b0)
      (ancWire D (D.labW - 1) hL) = decide (c = some 0) ∧
    evalRev (prepZero D) (Function.update (padTo (gammaW D) (gammaTaggedCode D c)) ⟨0, h0⟩ b0)
      (flagWire D) = c.isSome ∧
    evalRev (prepZero D) (Function.update (padTo (gammaW D) (gammaTaggedCode D c)) ⟨0, h0⟩ b0)
      ⟨0, h0⟩ = b0 := by
  set q0 := Function.update (padTo (gammaW D) (gammaTaggedCode D c)) ⟨0, h0⟩ b0
  set q1 := evalRev (prepZero D) q0
  have hL2 : 2 ≤ D.labW := two_le_labW D
  have hW : 2 * D.labW ≤ (D.r + 1) * D.labW := two_mul_labW_le_tagW D
  have hq0_flag : q0 (flagWire D) = c.isSome := by
    have hne : flagWire D ≠ ⟨0, h0⟩ := by simp [Fin.ext_iff, flagWire]
    have hq0f : q0 (flagWire D) = padTo (gammaW D) (gammaTaggedCode D c) (flagWire D) := by
      simp [q0, hne]
    rw [hq0f]
    have h1 : (flagWire D).val < 1 + (D.r + 1) * D.labW := by simp [flagWire]; omega
    simp only [padTo, dif_pos h1, gammaTaggedCode, boolAppCode, Fin.append]
    simp [flagWire, Fin.addCases]
    exact tagCode_xEmb_zero_bit D c
  have hq0_ctrl : ∀ j (hj : j < D.labW),
      q0 (ctrlWire D j hj) = Option.elim c false (fun α => α.val.testBit j) := by
    intro j hj
    have hne : ctrlWire D j hj ≠ ⟨0, h0⟩ := by simp [Fin.ext_iff, ctrlWire]
    have hq0c : q0 (ctrlWire D j hj) = padTo (gammaW D) (gammaTaggedCode D c) (ctrlWire D j hj) := by
      simp [q0, hne]
    rw [hq0c]
    have h1 : (ctrlWire D j hj).val < 1 + (D.r + 1) * D.labW := by simp [ctrlWire]; omega
    have hjlt : D.labW + j < (D.r + 1) * D.labW := by omega
    have hnat : (⟨(ctrlWire D j hj).val, h1⟩ : Fin (1 + (D.r + 1) * D.labW)) =
        Fin.natAdd 1 ⟨D.labW + j, hjlt⟩ := by
      ext; simp [ctrlWire]; omega
    simp only [padTo, dif_pos h1, gammaTaggedCode, boolAppCode]
    rw [hnat, Fin.append_right]
    cases c with
    | none =>
      simp [FieldData.xEmb, FieldData.tagCode, packNat, FieldData.digit]
    | some α =>
      simpa using tagCode_xEmb_lab_bit D α j hj
  have hflip := evalRev_flipCtrlAux D D.labW le_rfl q0
  set qf := evalRev (flipCtrlAux D D.labW le_rfl) q0
  have hqf_anc : ∀ j (hj : j < D.labW), qf (ancWire D j hj) = false := by
    intro j hj
    have hnotctrl : ∀ m (hm : m < D.labW), ancWire D j hj ≠ ctrlWire D m hm := by
      intro m hm; simp [Fin.ext_iff, ancWire, ctrlWire]; omega
    change qf (ancWire D j hj) = false
    rw [hflip.2 (ancWire D j hj) hnotctrl]
    have hne0 : ancWire D j hj ≠ ⟨0, h0⟩ := by simp [Fin.ext_iff, ancWire]
    have hq0a : q0 (ancWire D j hj) = padTo (gammaW D) (gammaTaggedCode D c) (ancWire D j hj) := by
      simp [q0, hne0]
    rw [hq0a]
    have hge : ¬ (ancWire D j hj).val < 1 + (D.r + 1) * D.labW := by simp [ancWire]
    simp [padTo, hge]
  have hqf_flag : qf (flagWire D) = c.isSome := by
    have hnotctrl : ∀ m (hm : m < D.labW), flagWire D ≠ ctrlWire D m hm := by
      intro m hm; simp [Fin.ext_iff, flagWire, ctrlWire]; omega
    change qf (flagWire D) = c.isSome
    rw [hflip.2 (flagWire D) hnotctrl, hq0_flag]
  have hcas := evalRev_cascadeAux D D.labW le_rfl qf hqf_anc
  have hq1_eq : q1 = evalRev (cascadeAux D D.labW le_rfl) qf := by
    simp [q1, prepZero, evalRev_append, qf]
  refine ⟨?_, ?_, ?_⟩
  · rw [hq1_eq, hcas.1 (D.labW - 1) (by omega), hqf_flag, show D.labW - 1 + 1 = D.labW by omega]
    cases c with
    | none => simp
    | some α =>
      simp only [Option.isSome_some, Bool.true_and, Option.some.injEq]
      have hall : (List.range D.labW).all (fun m => if hm : m < D.labW then qf (ctrlWire D m hm) else false) =
          decide (α = 0) := by
        rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq]
        constructor
        · intro h
          have hbit : ∀ j < D.labW, α.val.testBit j = false := by
            intro j hj
            have hmem := h j (List.mem_range.mpr hj)
            simp only [dif_pos hj] at hmem
            have hfj := hflip.1 j hj
            change qf (ctrlWire D j hj) = !q0 (ctrlWire D j hj) at hfj
            rw [hfj, hq0_ctrl j hj] at hmem
            simpa using hmem
          have hz := (testBit_eq_false_iff_zero (val_lt_two_pow_labW D α)).mp hbit
          exact ZMod.val_injective (D.q - 1) (by simpa using hz)
        · rintro rfl m hm
          rw [List.mem_range] at hm
          simp only [dif_pos hm]
          have hfj := hflip.1 m hm
          change qf (ctrlWire D m hm) = !q0 (ctrlWire D m hm) at hfj
          rw [hfj, hq0_ctrl m hm]
          simp
      exact hall
  · rw [hq1_eq, hcas.2 (flagWire D) (fun j hj => by simp [Fin.ext_iff, flagWire, ancWire]; omega), hqf_flag]
  · have hnt : ∀ g ∈ prepZero D, g.avoids 0 := by
      intro g hg
      simp only [prepZero, List.mem_append] at hg
      rcases hg with hg | hg
      · exact flipCtrlAux_not_touch0 D D.labW le_rfl g hg
      · exact cascadeAux_not_touch0 D D.labW le_rfl g hg
    have hz0 : (⟨0, h0⟩ : Fin (gammaW D)).val = 0 := rfl
    dsimp [q1, q0]
    rw [evalRev_not_touch0 (prepZero D) hnt _ ⟨0, h0⟩ hz0 b0]
    simp

def gammaMarkCirc (D : FieldData) : List (Instr (gammaW D)) :=
  let ancLast := ancWire D (D.labW - 1) (by have := two_le_labW D; omega)
  let z0 : Fin (gammaW D) := ⟨0, by have := gammaW_gt_tagW D; omega⟩
  let copyOut : List (RevGate (gammaW D)) :=
    [.cnot (flagWire D) z0 (by simp [Fin.ext_iff, flagWire, z0]),
     .cnot ancLast z0 (by simp [Fin.ext_iff, ancLast, ancWire, z0])]
  compileRev (shiftUp D ++ prepZero D) ++ [.s ancLast, .s ancLast] ++
    compileRev (copyOut ++ (prepZero D).reverse)

def gammaUnmarkCirc (D : FieldData) : List (Instr (gammaW D)) :=
  let ancLast := ancWire D (D.labW - 1) (by have := two_le_labW D; omega)
  let z0 : Fin (gammaW D) := ⟨0, by have := gammaW_gt_tagW D; omega⟩
  let copyOut : List (RevGate (gammaW D)) :=
    [.cnot (flagWire D) z0 (by simp [Fin.ext_iff, flagWire, z0]),
     .cnot ancLast z0 (by simp [Fin.ext_iff, ancLast, ancWire, z0])]
  compileRev (prepZero D ++ copyOut ++ (prepZero D).reverse ++ (shiftUp D).reverse)

lemma prepZero_rev_not_touch0 (D : FieldData) :
    ∀ g ∈ (prepZero D).reverse, g.avoids 0 := by
  intro g hg
  rw [List.mem_reverse] at hg
  simp only [prepZero, List.mem_append] at hg
  rcases hg with hg | hg
  · exact flipCtrlAux_not_touch0 D D.labW le_rfl g hg
  · exact cascadeAux_not_touch0 D D.labW le_rfl g hg

lemma xor_isSome_someZero (D : FieldData) (c : Option D.Lab) :
    xor c.isSome (decide (c = some 0)) = isNontrivLab c := by
  cases c with
  | none => rfl
  | some α =>
    by_cases hα : α = 0
    · subst hα; simp [isNontrivLab]
    · simp [isNontrivLab, hα]

lemma gammaMarkCirc_implements (D : FieldData) (ε : ℝ) (hε : 0 ≤ ε) :
    Implements (circUnitary (gammaMarkCirc D))
      (fun c => padTo (gammaW D) (D.tagCode (D.xEmb c)))
      (fun c => padTo (gammaW D) (gammaTaggedCode D c))
      (Matrix.diagonal fun c => match c with | none => 1 | some α => if α = 0 then -1 else 1) ε := by
  apply implements_of_act_ket_diagonal _ _ _ _ _ ε hε
  intro c
  have h0 : 0 < gammaW D := by have := gammaW_gt_tagW D; omega
  have hL : D.labW - 1 < D.labW := by have := two_le_labW D; omega
  let ancLast := ancWire D (D.labW - 1) hL
  let z0 : Fin (gammaW D) := ⟨0, h0⟩
  let copyOut : List (RevGate (gammaW D)) :=
    [.cnot (flagWire D) z0 (by simp [Fin.ext_iff, flagWire, z0]),
     .cnot ancLast z0 (by simp [Fin.ext_iff, ancLast, ancWire, z0])]
  have hsplit : gammaMarkCirc D =
      compileRev (shiftUp D ++ prepZero D) ++ [.s ancLast, .s ancLast] ++
        compileRev (copyOut ++ (prepZero D).reverse) := rfl
  rw [hsplit]
  simp only [circUnitary_append, act_mul, circUnitary_compileRev, instr_s_s_unitary, act_permMat,
    act_diagonal]
  rw [evalRev_append, evalRev_shiftUp_tagCode D c]
  have hprep := evalRev_prepZero_ancLast D c false h0 hL
  set q1 := evalRev (prepZero D) (Function.update (padTo (gammaW D) (gammaTaggedCode D c)) z0 false)
  have hphase : (if q1 ancLast then (-1 : ℂ) else 1) =
      (if c = some 0 then (-1 : ℂ) else 1) := by
    change (if q1 (ancWire D (D.labW - 1) hL) then (-1 : ℂ) else 1) = _
    rw [hprep.1]
    by_cases hc : c = some 0 <;> simp [hc]
  rw [hphase, act_smul, act_permMat, evalRev_append]
  have hcopy : evalRev copyOut q1 = Function.update q1 z0 (isNontrivLab c) := by
    have hf : flagWire D ≠ z0 := by simp [Fin.ext_iff, flagWire, z0]
    have ha : ancLast ≠ z0 := by simp [Fin.ext_iff, ancLast, ancWire, z0]
    funext x
    simp only [copyOut, evalRev_cons, evalRev_nil, RevGate.eval]
    by_cases hxz : x = z0
    · subst hxz
      rw [Function.update_self, Function.update_of_ne ha, Function.update_self]
      have hanc_eq : q1 ancLast = decide (c = some 0) := hprep.1
      rw [hprep.2.2, hprep.2.1, hanc_eq, Bool.false_xor, xor_isSome_someZero, Function.update_self]
    · simp [hxz]
  rw [hcopy]
  have hz0 : z0.val = 0 := rfl
  rw [evalRev_not_touch0 (prepZero D).reverse (prepZero_rev_not_touch0 D) q1 z0 hz0 (isNontrivLab c)]
  have hrev : evalRev (prepZero D).reverse q1 =
      Function.update (padTo (gammaW D) (gammaTaggedCode D c)) z0 false :=
    evalRev_reverse (prepZero D) _
  rw [hrev]
  have hfinal : Function.update (Function.update (padTo (gammaW D) (gammaTaggedCode D c)) z0 false) z0 (isNontrivLab c) =
      padTo (gammaW D) (gammaTaggedCode D c) := by
    funext x
    by_cases hxz : x = z0
    · subst hxz
      simp [z0, padTo, gammaTaggedCode, boolAppCode, Fin.append, Fin.addCases]
    · simp [hxz]
  rw [hfinal]
  cases c with
  | none => simp
  | some α => by_cases hα : α = 0 <;> simp [hα]

lemma gammaUnmarkCirc_implements (D : FieldData) (ε : ℝ) (hε : 0 ≤ ε) :
    Implements (circUnitary (gammaUnmarkCirc D))
      (fun c => padTo (gammaW D) (gammaTaggedCode D c))
      (fun c => padTo (gammaW D) (D.tagCode (D.xEmb c)))
      1 ε := by
  apply implements_of_act_ket_one _ _ _ _ ε hε
  intro c
  have h0 : 0 < gammaW D := by have := gammaW_gt_tagW D; omega
  have hL : D.labW - 1 < D.labW := by have := two_le_labW D; omega
  let ancLast := ancWire D (D.labW - 1) hL
  let z0 : Fin (gammaW D) := ⟨0, h0⟩
  let copyOut : List (RevGate (gammaW D)) :=
    [.cnot (flagWire D) z0 (by simp [Fin.ext_iff, flagWire, z0]),
     .cnot ancLast z0 (by simp [Fin.ext_iff, ancLast, ancWire, z0])]
  have hsplit : gammaUnmarkCirc D =
      compileRev (prepZero D ++ copyOut ++ (prepZero D).reverse ++ (shiftUp D).reverse) := rfl
  rw [hsplit, circUnitary_compileRev, act_permMat]
  simp only [evalRev_append]
  have hq0_upd : padTo (gammaW D) (gammaTaggedCode D c) =
      Function.update (padTo (gammaW D) (gammaTaggedCode D c)) z0 (isNontrivLab c) := by
    funext x
    by_cases hxz : x = z0
    · subst hxz
      simp [z0, padTo, gammaTaggedCode, boolAppCode, Fin.append, Fin.addCases]
    · simp [hxz]
  rw [hq0_upd]
  have hprep := evalRev_prepZero_ancLast D c (isNontrivLab c) h0 hL
  set q1 := evalRev (prepZero D) (Function.update (padTo (gammaW D) (gammaTaggedCode D c)) z0 (isNontrivLab c))
  have hcopy : evalRev copyOut q1 = Function.update q1 z0 false := by
    have hf : flagWire D ≠ z0 := by simp [Fin.ext_iff, flagWire, z0]
    have ha : ancLast ≠ z0 := by simp [Fin.ext_iff, ancLast, ancWire, z0]
    funext x
    simp only [copyOut, evalRev_cons, evalRev_nil, RevGate.eval]
    by_cases hxz : x = z0
    · subst hxz
      rw [Function.update_self, Function.update_of_ne ha, Function.update_self]
      have hanc_eq : q1 ancLast = decide (c = some 0) := hprep.1
      rw [hprep.2.2, hprep.2.1, hanc_eq, Bool.xor_assoc, xor_isSome_someZero, Bool.xor_self, Function.update_self]
    · simp [hxz]
  rw [hcopy]
  have hz0 : z0.val = 0 := rfl
  rw [evalRev_not_touch0 (prepZero D).reverse (prepZero_rev_not_touch0 D) q1 z0 hz0 false]
  have hrev : evalRev (prepZero D).reverse q1 =
      Function.update (padTo (gammaW D) (gammaTaggedCode D c)) z0 (isNontrivLab c) :=
    evalRev_reverse (prepZero D) _
  rw [hrev]
  have hupd_f : Function.update (Function.update (padTo (gammaW D) (gammaTaggedCode D c)) z0 (isNontrivLab c)) z0 false =
      Function.update (padTo (gammaW D) (gammaTaggedCode D c)) z0 false := by
    funext x; by_cases hx : x = z0 <;> simp [hx]
  rw [hupd_f, ← evalRev_shiftUp_tagCode D c, evalRev_reverse]

/-! ### Section 4: Raw circuit compilation, `PolyTimeComputable` builders, and gate-count bounds -/

section PolyTimeSection

open OAI.MetricKMedian.Binary QAlgorithms.LocalHamiltonian

lemma natBits_length_le_iff {n k : ℕ} : n.bits.length ≤ k ↔ n < 2 ^ k := by
  induction n using Nat.binaryRec generalizing k with
  | zero => simp
  | bit b n ih =>
    by_cases h0 : n = 0 ∧ b = false
    · rcases h0 with ⟨rfl, rfl⟩
      simp [Nat.bit]
    · have hne : n = 0 → b = true := fun hn => by cases hb : b <;> simp_all
      rw [Nat.bits_append_bit n b hne, List.length_cons]
      have hbv := Nat.bit_val b n
      cases k with
      | zero =>
        simp only [Nat.pow_zero]
        constructor <;> intro h <;> cases b <;> simp_all
      | succ k =>
        rw [Nat.pow_succ']
        have ihk := @ih k
        cases b <;> simp only [Bool.toNat_true, Bool.toNat_false] at hbv <;> omega

lemma bits_length_sub_one_eq_clog2 {m : ℕ} (hm : 1 ≤ m) :
    (m - 1).bits.length = Nat.clog 2 m := by
  apply Nat.le_antisymm
  · rw [natBits_length_le_iff]
    have h := (Nat.clog_le_iff_le_pow (by decide) (x := m) (y := Nat.clog 2 m)).mp le_rfl
    omega
  · rw [Nat.clog_le_iff_le_pow (by decide)]
    have h := natBits_length_le_iff.mp (le_refl (m - 1).bits.length)
    omega

@[fun_prop]
lemma poly_natBits : Automatic.Poly Nat.bits :=
  ⟨BooleanLists.packProgram.recode Nat.bits (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop]
lemma poly_natBits_comp {α : Type} [Automatic.Coding α] {f : α → ℕ} (hf : Automatic.Poly f) :
    Automatic.Poly (fun x => (f x).bits) := by
  rcases hf with ⟨Pf⟩
  rcases poly_natBits with ⟨Pb⟩
  exact ⟨(Pf.comp Pb).congr _ (fun _ => rfl)⟩

@[fun_prop]
lemma poly_natBodd : Automatic.Poly Nat.bodd :=
  ⟨PolyProgram.natOdd⟩

@[fun_prop]
lemma poly_natBodd_comp {α : Type} [Automatic.Coding α] {f : α → ℕ} (hf : Automatic.Poly f) :
    Automatic.Poly (fun x => (f x).bodd) := by
  rcases hf with ⟨Pf⟩
  exact ⟨(Pf.comp PolyProgram.natOdd).congr _ (fun _ => rfl)⟩

@[fun_prop]
lemma poly_listReverse {α : Type} [Automatic.Coding α] [Inhabited α] :
    Automatic.Poly (List.reverse : List α → List α) :=
  ⟨PolyProgram.listReverse Automatic.enc default⟩

@[fun_prop]
lemma poly_listReverse_comp {α β : Type} [Automatic.Coding α] [Automatic.Coding β] [Inhabited β]
    {l : α → List β} (hl : Automatic.Poly l) :
    Automatic.Poly (fun x => (l x).reverse) := by
  rcases hl with ⟨Pl⟩
  exact ⟨(Pl.comp (PolyProgram.listReverse Automatic.enc default)).congr _ (fun _ => rfl)⟩

@[fun_prop]
lemma poly_list_indices_comp {α β : Type} [Automatic.Coding α] [Automatic.Coding β] [Inhabited β]
    {l : α → List β} (hl : Automatic.Poly l) :
    Automatic.Poly (fun x => List.range (l x).length) := by
  rcases hl with ⟨Pl⟩
  rcases (Automatic.Poly.list_indices : Automatic.Poly fun xs : List β => List.range xs.length) with ⟨Pi⟩
  exact ⟨(Pl.comp Pi).congr _ (fun _ => rfl)⟩

def decodeBits (bs : List Bool) : ℕ :=
  bs.reverse.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0

lemma decodeBits_bits (n : ℕ) : decodeBits n.bits = n := by
  induction n using Nat.binaryRec with
  | zero => rfl
  | bit b n ih =>
    by_cases h0 : n = 0 ∧ b = false
    · rcases h0 with ⟨rfl, rfl⟩; simp [Nat.bit, decodeBits]
    · have hne : n = 0 → b = true := fun hn => by cases hb : b <;> simp_all
      simp only [decodeBits, Nat.bits_append_bit n b hne, List.reverse_cons, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      change 2 * decodeBits n.bits + (if b then 1 else 0) = Nat.bit b n
      rw [ih, Nat.bit_val]
      cases b <;> simp

lemma natBits_mul_length_le (x y : ℕ) :
    (x * y).bits.length ≤ x.bits.length + y.bits.length := by
  rw [natBits_length_le_iff, Nat.pow_add]
  have hx := natBits_length_le_iff.mp (le_refl x.bits.length)
  have hy := natBits_length_le_iff.mp (le_refl y.bits.length)
  exact Nat.mul_lt_mul_of_lt_of_lt hx hy

lemma encodeList_bits_sum_le (ps : List ℕ) :
    (ps.map (fun x => x.bits.length)).sum ≤ (encodeList Nat.bits ps).length := by
  induction ps with
  | nil => simp [EncodedList.nil]
  | cons a ps ih =>
    simp only [List.map_cons, List.sum_cons, EncodedList.cons_length]
    omega

lemma encodePair_length_eq {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (x : α) (y : β) :
    (encodePair ea eb (x, y)).length = 2 * (ea x).length + 1 + (eb y).length := by
  simp [encodePair, quote_length]

@[fun_prop]
lemma poly_decodeBits : Automatic.Poly decodeBits := by
  have hop : Automatic.Poly (fun p : ℕ × Bool => 2 * p.1 + if p.2 then 1 else 0) := by fun_prop
  rcases hop with ⟨Pop⟩
  have Pop' : PolyProgram (encodePair Nat.bits encodeBool) Nat.bits
      (fun p : ℕ × Bool => 2 * p.1 + if p.2 then 1 else 0) := Pop
  have hfold : PolyProgram (encodePair (encodeList encodeBool) Nat.bits) Nat.bits
      (fun x : List Bool × ℕ => List.foldl (fun acc b => 2 * acc + if b then 1 else 0) x.2 x.1) := by
    refine PolyProgram.listFold Pop' false Polynomial.X ?_
    intro as b pre suf hsplit
    have hpre_bound : ∀ (pre : List Bool) (b : ℕ),
        (List.foldl (fun acc (a : Bool) => 2 * acc + if a then 1 else 0) b pre).bits.length ≤
          b.bits.length + pre.length := by
      intro p0 b0
      induction p0 generalizing b0 with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.foldl_cons, List.length_cons]
        have hstep : (2 * b0 + if hd then 1 else 0).bits.length ≤ b0.bits.length + 1 := by
          rw [natBits_length_le_iff, Nat.pow_succ']
          have hb0 := natBits_length_le_iff.mp (le_refl b0.bits.length)
          cases hd <;> simp <;> omega
        exact (ih _).trans (by omega)
    have h1 := hpre_bound pre b
    have hlen_pre : pre.length ≤ as.length := by rw [hsplit]; simp
    have hlen_as : as.length ≤ (encodeList encodeBool as).length := EncodedList.length_le encodeBool as
    have hp := encodePair_length_eq (encodeList encodeBool) Nat.bits as b
    simp only [Polynomial.eval_X]
    omega
  have hprepA : Automatic.Poly (fun bs : List Bool => (bs.reverse, (0 : ℕ))) := by fun_prop
  rcases hprepA with ⟨Pprep⟩
  exact ⟨(Pprep.comp hfold).congr _ (fun _ => rfl)⟩

@[fun_prop]
lemma poly_decodeBits_comp {α : Type} [Automatic.Coding α] {bs : α → List Bool} (hbs : Automatic.Poly bs) :
    Automatic.Poly (fun x => decodeBits (bs x)) := by
  rcases hbs with ⟨Pbs⟩
  rcases poly_decodeBits with ⟨Pd⟩
  exact ⟨(Pbs.comp Pd).congr _ (fun _ => rfl)⟩

def prodList (as : List ℕ) : ℕ := as.foldl (· * ·) 1

@[fun_prop]
lemma poly_prodList : Automatic.Poly prodList := by
  have hop : Automatic.Poly (fun p : ℕ × ℕ => p.1 * p.2) := by fun_prop
  rcases hop with ⟨Pop⟩
  have Pop' : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun p : ℕ × ℕ => p.1 * p.2) := Pop
  have hfold : PolyProgram (encodePair (encodeList Nat.bits) Nat.bits) Nat.bits
      (fun x : List ℕ × ℕ => List.foldl (· * ·) x.2 x.1) := by
    refine PolyProgram.listFold Pop' 0 Polynomial.X ?_
    intro as b pre suf hsplit
    have hpre_bound : ∀ (pre : List ℕ) (b : ℕ),
        (List.foldl (· * ·) b pre).bits.length ≤
          b.bits.length + (pre.map (fun x => x.bits.length)).sum := by
      intro p0 b0
      induction p0 generalizing b0 with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        exact (ih (b0 * hd)).trans (by have := natBits_mul_length_le b0 hd; omega)
    have h1 := hpre_bound pre b
    have hsum : (pre.map (fun x => x.bits.length)).sum ≤ (encodeList Nat.bits as).length := by
      have ha : encodeList Nat.bits as = encodeList Nat.bits pre ++ encodeList Nat.bits suf := by
        rw [hsplit, EncodedList.append]
      have hle : (encodeList Nat.bits pre).length ≤ (encodeList Nat.bits as).length := by
        rw [ha, List.length_append]; omega
      exact (encodeList_bits_sum_le pre).trans hle
    have hp := encodePair_length_eq (encodeList Nat.bits) Nat.bits as b
    simp only [Polynomial.eval_X]
    omega
  have hprepA : Automatic.Poly (fun as : List ℕ => (as, (1 : ℕ))) := by fun_prop
  rcases hprepA with ⟨Pprep⟩
  exact ⟨(Pprep.comp hfold).congr _ (fun _ => rfl)⟩

@[fun_prop]
lemma poly_prodList_comp {α : Type} [Automatic.Coding α] {as : α → List ℕ} (has : Automatic.Poly as) :
    Automatic.Poly (fun x => prodList (as x)) := by
  rcases has with ⟨Pas⟩
  rcases poly_prodList with ⟨Pp⟩
  exact ⟨(Pas.comp Pp).congr _ (fun _ => rfl)⟩

lemma prodList_replicate (n p : ℕ) : prodList (List.replicate n p) = p ^ n := by
  unfold prodList
  have h : ∀ (acc : ℕ), (List.replicate n p).foldl (· * ·) acc = acc * p ^ n := by
    intro acc
    induction n generalizing acc with
    | zero => simp
    | succ n ih =>
      rw [List.replicate_succ, List.foldl_cons, ih, pow_succ', mul_assoc]
  simpa using h 1

lemma encBin_length (m : ℕ) : (encBin m).length = 2 * m.bits.length + 2 := by
  simp only [encBin, List.length_append, List.length_cons, List.length_nil, List.length_flatMap]
  induction m.bits with
  | nil => simp
  | cons b tl ih => simp; omega

lemma bodd_two_mul (k : ℕ) : Nat.bodd (2 * k) = false := by
  simp [Nat.bodd_mul]

lemma bodd_two_mul_add_one (k : ℕ) : Nat.bodd (2 * k + 1) = true := by
  rw [Nat.bodd_add, bodd_two_mul]; rfl

lemma flatMap_pair_length (bs : List Bool) :
    (bs.flatMap (fun β => [true, β])).length = 2 * bs.length := by
  induction bs with
  | nil => simp
  | cons b tl ih => simp [List.flatMap_cons, ih]; omega

lemma flatMap_pair_getElem?_even (bs : List Bool) (j : ℕ) (hj : j < bs.length) :
    (bs.flatMap (fun β => [true, β]))[2 * j]? = some true := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b tl ih =>
    cases j with
    | zero => simp [List.flatMap_cons]
    | succ j =>
      have hj' : j < tl.length := Nat.lt_of_succ_lt_succ hj
      simp only [List.flatMap_cons, List.cons_append, Nat.mul_succ, List.getElem?_cons_succ]
      exact ih j hj'

lemma flatMap_pair_getElem?_odd (bs : List Bool) (j : ℕ) (hj : j < bs.length) :
    (bs.flatMap (fun β => [true, β]))[2 * j + 1]? = some bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b tl ih =>
    cases j with
    | zero => simp [List.flatMap_cons]
    | succ j =>
      have hj' : j < tl.length := Nat.lt_of_succ_lt_succ hj
      simp only [List.flatMap_cons, List.cons_append, Nat.mul_succ, List.getElem?_cons_succ]
      exact ih j hj'

def binEndAfter (xs : List Bool) (start : ℕ) : ℕ :=
  ((List.range xs.length).filter (fun i => decide (start ≤ i) && !Nat.bodd i && !xs[i]?.getD false)).head?.getD 0

@[fun_prop]
lemma poly_binEndAfter_pair : Automatic.Poly (fun p : List Bool × ℕ => binEndAfter p.1 p.2) := by
  unfold binEndAfter
  fun_prop

@[fun_prop]
lemma poly_binEndAfter_comp {α : Type} [Automatic.Coding α] {xs : α → List Bool} {s : α → ℕ}
    (hxs : Automatic.Poly xs) (hs : Automatic.Poly s) :
    Automatic.Poly (fun x => binEndAfter (xs x) (s x)) := by
  rcases hxs with ⟨Pxs⟩
  rcases hs with ⟨Ps⟩
  rcases poly_binEndAfter_pair with ⟨Pb⟩
  exact ⟨((Pxs.fanout Ps).comp Pb).congr _ (fun _ => rfl)⟩

def parseBinFrom (xs : List Bool) (start : ℕ) : ℕ :=
  decodeBits
    (((List.range xs.length).filter
      (fun i => decide (start ≤ i) && decide (i < binEndAfter xs start) && Nat.bodd i)).map
      (fun i => xs[i]?.getD false))

@[fun_prop]
lemma poly_parseBinFrom_pair : Automatic.Poly (fun p : List Bool × ℕ => parseBinFrom p.1 p.2) := by
  unfold parseBinFrom
  fun_prop

@[fun_prop]
lemma poly_parseBinFrom_comp {α : Type} [Automatic.Coding α] {xs : α → List Bool} {s : α → ℕ}
    (hxs : Automatic.Poly xs) (hs : Automatic.Poly s) :
    Automatic.Poly (fun x => parseBinFrom (xs x) (s x)) := by
  rcases hxs with ⟨Pxs⟩
  rcases hs with ⟨Ps⟩
  rcases poly_parseBinFrom_pair with ⟨Pp⟩
  exact ⟨((Pxs.fanout Ps).comp Pp).congr _ (fun _ => rfl)⟩

lemma head_eq_of_pairwise_le {l : List ℕ} (hp : l.Pairwise (· ≤ ·)) {e : ℕ} (he : e ∈ l)
    (hmin : ∀ x ∈ l, e ≤ x) : l.head?.getD 0 = e := by
  cases l with
  | nil => simp at he
  | cons a tl =>
    simp only [Option.getD_some, List.head?_cons]
    simp only [List.mem_cons] at he
    rcases he with rfl | hetl
    · rfl
    · have ha_le_e : a ≤ e := (List.pairwise_cons.mp hp).1 e hetl
      have he_le_a : e ≤ a := hmin a (List.mem_cons_self)
      omega

lemma range_pairwise_lt (n : ℕ) : (List.range n).Pairwise (· < ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    exact ⟨ih, List.pairwise_singleton _ _, fun a ha b hb => by
      simp only [List.mem_range, List.mem_singleton] at ha hb; omega⟩

lemma binEndAfter_eq (pre : List Bool) (m : ℕ) (suf : List Bool)
    (heven : ∃ s, pre.length = 2 * s) :
    binEndAfter (pre ++ encBin m ++ suf) pre.length = pre.length + 2 * m.bits.length := by
  rcases heven with ⟨s, hs⟩
  set xs := pre ++ encBin m ++ suf
  set start := pre.length
  set e := start + 2 * m.bits.length
  set l := (List.range xs.length).filter (fun i => decide (start ≤ i) && !Nat.bodd i && !xs[i]?.getD false)
  have hxs_len : e + 1 < xs.length := by
    simp [xs, e, start, List.length_append, encBin_length]; omega
  have hxs_e : xs[e]? = some false := by
    have h1 : xs = pre ++ (encBin m ++ suf) := by simp [xs, List.append_assoc]
    rw [h1, List.getElem?_append_right (by omega : pre.length ≤ e)]
    simp only [e, start, Nat.add_sub_cancel_left, encBin, List.append_assoc]
    rw [List.getElem?_append_right (by rw [flatMap_pair_length]), flatMap_pair_length]
    simp
  have he_even : Nat.bodd e = false := by
    rw [show e = 2 * (s + m.bits.length) by omega, bodd_two_mul]
  have he_mem : e ∈ l := by
    simp only [l, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    exact ⟨by omega, ⟨⟨by omega, he_even⟩, by simp [hxs_e]⟩⟩
  have hmin : ∀ i ∈ l, e ≤ i := by
    intro i hi
    simp only [l, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hi
    rcases hi with ⟨hilt, ⟨⟨hsi, hbodd⟩, hxfalse⟩⟩
    by_contra hlt
    have hie : i < e := by omega
    have hidx_even : ∃ j, i = start + 2 * j ∧ j < m.bits.length := by
      have hmod : i % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one i with h | h
        · exact h
        · exfalso
          have hi_eq : i = 2 * (i / 2) + 1 := by omega
          rw [hi_eq, bodd_two_mul_add_one] at hbodd
          cases hbodd
      refine ⟨(i - start) / 2, by omega, by omega⟩
    rcases hidx_even with ⟨j, rfl, hj⟩
    have h1 : xs = pre ++ (encBin m ++ suf) := by simp [xs, List.append_assoc]
    have hxs_i : xs[start + 2 * j]? = some true := by
      rw [h1, List.getElem?_append_right (by omega : pre.length ≤ start + 2 * j)]
      simp only [start, Nat.add_sub_cancel_left, encBin, List.append_assoc]
      rw [List.getElem?_append_left (by rw [flatMap_pair_length]; omega)]
      exact flatMap_pair_getElem?_even m.bits j hj
    simp [hxs_i] at hxfalse
  have hpw : l.Pairwise (· ≤ ·) :=
    ((range_pairwise_lt xs.length).filter _).imp (fun h => le_of_lt h)
  exact head_eq_of_pairwise_le hpw he_mem hmin

lemma filter_range_odd_between_exact (s L : ℕ) :
    ((List.range (2 * s + 2 * L)).filter (fun i => decide (2 * s ≤ i) && Nat.bodd i)) =
      (List.range L).map (fun j => 2 * s + 2 * j + 1) := by
  induction L with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, List.range_zero, List.map_nil, List.filter_eq_nil_iff]
    intro i hi
    rw [List.mem_range] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨h1, _⟩
    omega
  | succ L ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, Nat.add_succ, Nat.add_succ, List.range_succ, List.range_succ]
    simp only [List.filter_append, List.filter_cons, List.filter_nil, List.range_succ, List.map_append,
      List.map_singleton]
    have h1 : (decide (2 * s ≤ 2 * s + 2 * L) && Nat.bodd (2 * s + 2 * L)) = false := by
      rw [show 2 * s + 2 * L = 2 * (s + L) by omega, bodd_two_mul]; simp
    have h2 : (decide (2 * s ≤ 2 * s + 2 * L + 1) && Nat.bodd (2 * s + 2 * L + 1)) = true := by
      have hge : decide (2 * s ≤ 2 * s + 2 * L + 1) = true := decide_eq_true (by omega)
      rw [hge, show 2 * s + 2 * L + 1 = 2 * (s + L) + 1 by omega, bodd_two_mul_add_one]; rfl
    rw [h1, h2, ih]
    simp

lemma filter_range_odd_between (N s L : ℕ) (hN : 2 * s + 2 * L ≤ N) :
    ((List.range N).filter (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * L) && Nat.bodd i)) =
      (List.range L).map (fun j => 2 * s + 2 * j + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction d with
  | zero =>
    simp only [Nat.add_zero]
    rw [← filter_range_odd_between_exact s L]
    apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    simp [hi]
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
    have hnot : ¬ (2 * s + 2 * L + d < 2 * s + 2 * L) := by omega
    simp only [decide_eq_false hnot, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      List.append_nil]
    exact ih (by omega)

lemma parseBinFrom_eq (pre : List Bool) (m : ℕ) (suf : List Bool)
    (heven : ∃ s, pre.length = 2 * s) :
    parseBinFrom (pre ++ encBin m ++ suf) pre.length = m := by
  rcases heven with ⟨s, hs⟩
  rw [parseBinFrom, binEndAfter_eq pre m suf ⟨s, hs⟩, hs]
  have hN : 2 * s + 2 * m.bits.length ≤ (pre ++ encBin m ++ suf).length := by
    simp only [List.length_append, hs, encBin_length]; omega
  rw [filter_range_odd_between _ s m.bits.length hN]
  have hmap : ((List.range m.bits.length).map (fun j => 2 * s + 2 * j + 1)).map
      (fun i => (pre ++ encBin m ++ suf)[i]?.getD false) = m.bits := by
    rw [List.map_map]
    apply List.ext_getElem
    · simp
    · intro j hj1 hj2
      simp only [List.getElem_map, List.getElem_range, Function.comp_def]
      have h1 : pre ++ encBin m ++ suf = pre ++ (encBin m ++ suf) := by simp [List.append_assoc]
      rw [h1, List.getElem?_append_right (by omega : pre.length ≤ 2 * s + 2 * j + 1), hs]
      rw [show 2 * s + 2 * j + 1 - 2 * s = 2 * j + 1 by omega]
      simp only [encBin, List.append_assoc]
      rw [List.getElem?_append_left (by rw [flatMap_pair_length]; omega)]
      rw [flatMap_pair_getElem?_odd m.bits j hj2]
      rfl
  rw [hmap, decodeBits_bits]

lemma filter_range_lt_eq {N n : ℕ} (hn : n ≤ N) :
    (List.range N).filter (fun i => decide (i < n)) = List.range n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero =>
    simp only [Nat.add_zero]
    have h : (List.range n).filter (fun i => decide (i < n)) = (List.range n).filter (fun _ => true) :=
      List.filter_congr (fun i hi => by rw [List.mem_range] at hi; simp [hi])
    rw [h, List.filter_true]
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
    have hnot : ¬ (n + d < n) := by omega
    simp only [decide_eq_false hnot, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    exact ih (by omega)

def pRaw (xs : List Bool) : ℕ := parseBinFrom xs 0
def pEndRaw (xs : List Bool) : ℕ := binEndAfter xs 0
def rRaw (xs : List Bool) : ℕ := parseBinFrom xs (pEndRaw xs + 2)
def qRaw (xs : List Bool) : ℕ :=
  prodList (((List.range xs.length).filter (fun i => decide (i < rRaw xs))).map (fun _ => pRaw xs))
def labWRaw (xs : List Bool) : ℕ :=
  (qRaw xs * qRaw xs - 1).bits.length
def tagWRaw (xs : List Bool) : ℕ :=
  (rRaw xs + 1) * labWRaw xs
def gammaWRaw (xs : List Bool) : ℕ :=
  1 + tagWRaw xs + labWRaw xs

@[fun_prop] lemma poly_pRaw : Automatic.Poly pRaw := by unfold pRaw; fun_prop
@[fun_prop] lemma poly_pEndRaw : Automatic.Poly pEndRaw := by unfold pEndRaw; fun_prop
@[fun_prop] lemma poly_rRaw : Automatic.Poly rRaw := by unfold rRaw; fun_prop
@[fun_prop] lemma poly_qRaw : Automatic.Poly qRaw := by unfold qRaw; fun_prop
@[fun_prop] lemma poly_labWRaw : Automatic.Poly labWRaw := by unfold labWRaw; fun_prop
@[fun_prop] lemma poly_tagWRaw : Automatic.Poly tagWRaw := by unfold tagWRaw; fun_prop
@[fun_prop] lemma poly_gammaWRaw : Automatic.Poly gammaWRaw := by unfold gammaWRaw; fun_prop

lemma flatMap_encBin_length_ge (l : List ℕ) (f : ℕ → ℕ) :
    2 * l.length ≤ (l.flatMap (fun j => encBin (f j))).length := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, encBin_length]
    omega

lemma encData_eq_encBin_p_r (D : FieldData) :
    ∃ suf : List Bool, D.encData = encBin D.p ++ encBin D.r ++ suf := by
  unfold FieldData.encData
  simp only [List.append_assoc]
  exact ⟨_, rfl⟩

lemma encData_length_ge_r (D : FieldData) : D.r ≤ D.encData.length := by
  unfold FieldData.encData
  have h1 := flatMap_encBin_length_ge (List.range (D.r + 1)) (fun j => (D.f.coeff j).val)
  simp only [List.length_range] at h1
  simp only [List.length_append]
  omega

lemma encData_length_ge_p_bits (D : FieldData) : D.p.bits.length ≤ D.encData.length := by
  obtain ⟨suf, hsuf⟩ := encData_eq_encBin_p_r D
  rw [hsuf, List.length_append, List.length_append, encBin_length]
  omega

lemma pRaw_encData (D : FieldData) (k : ℕ) : pRaw (D.encData ++ encNat k) = D.p := by
  obtain ⟨suf, hsuf⟩ := encData_eq_encBin_p_r D
  unfold pRaw
  have h : D.encData ++ encNat k = [] ++ encBin D.p ++ (encBin D.r ++ suf ++ encNat k) := by
    rw [hsuf]; simp [List.append_assoc]
  rw [h]
  exact parseBinFrom_eq [] D.p (encBin D.r ++ suf ++ encNat k) ⟨0, rfl⟩

lemma pEndRaw_encData (D : FieldData) (k : ℕ) :
    pEndRaw (D.encData ++ encNat k) = 2 * D.p.bits.length := by
  obtain ⟨suf, hsuf⟩ := encData_eq_encBin_p_r D
  unfold pEndRaw
  have h : D.encData ++ encNat k = [] ++ encBin D.p ++ (encBin D.r ++ suf ++ encNat k) := by
    rw [hsuf]; simp [List.append_assoc]
  rw [h]
  simpa using binEndAfter_eq [] D.p (encBin D.r ++ suf ++ encNat k) ⟨0, rfl⟩

lemma rRaw_encData (D : FieldData) (k : ℕ) : rRaw (D.encData ++ encNat k) = D.r := by
  obtain ⟨suf, hsuf⟩ := encData_eq_encBin_p_r D
  unfold rRaw
  rw [pEndRaw_encData D k]
  have hpre : (encBin D.p).length = 2 * D.p.bits.length + 2 := encBin_length D.p
  have h : D.encData ++ encNat k = encBin D.p ++ encBin D.r ++ (suf ++ encNat k) := by
    rw [hsuf]; simp [List.append_assoc]
  rw [h, ← hpre]
  exact parseBinFrom_eq (encBin D.p) D.r (suf ++ encNat k) ⟨D.p.bits.length + 1, by rw [hpre]; omega⟩

lemma qRaw_encData (D : FieldData) (k : ℕ) : qRaw (D.encData ++ encNat k) = D.q := by
  unfold qRaw
  rw [rRaw_encData, pRaw_encData]
  have hr : D.r ≤ (D.encData ++ encNat k).length := (encData_length_ge_r D).trans (by simp)
  rw [filter_range_lt_eq hr]
  have hrep : (List.range D.r).map (fun _ => D.p) = List.replicate D.r D.p := by
    apply List.ext_getElem <;> simp
  rw [hrep, prodList_replicate]
  rfl

lemma labWRaw_encData (D : FieldData) (k : ℕ) : labWRaw (D.encData ++ encNat k) = D.labW := by
  unfold labWRaw FieldData.labW
  rw [qRaw_encData, ← sq]
  have hq : 1 ≤ D.q ^ 2 := by have := D.one_lt_q; nlinarith
  exact bits_length_sub_one_eq_clog2 hq

lemma tagWRaw_encData (D : FieldData) (k : ℕ) : tagWRaw (D.encData ++ encNat k) = (D.r + 1) * D.labW := by
  unfold tagWRaw
  rw [rRaw_encData, labWRaw_encData]

lemma gammaWRaw_encData (D : FieldData) (k : ℕ) : gammaWRaw (D.encData ++ encNat k) = gammaW D := by
  unfold gammaWRaw gammaW
  rw [tagWRaw_encData, labWRaw_encData]

def toRawInstr {m : ℕ} : Instr m → ℕ × ℕ × ℕ
  | .h i => (0, i.val, 0)
  | .s i => (1, i.val, 0)
  | .t i => (2, i.val, 0)
  | .x i => (3, i.val, 0)
  | .cnot i j _ => (4, i.val, j.val)

def rawCcx3 : List (ℕ × ℕ × ℕ) := ccx3.map toRawInstr

def rawCcx (a b c : ℕ) : List (ℕ × ℕ × ℕ) :=
  rawCcx3.map (fun g =>
    (g.1,
     if g.2.1 = 0 then a else if g.2.1 = 1 then b else c,
     if g.1 = 4 then (if g.2.2 = 0 then a else if g.2.2 = 1 then b else c) else 0))

@[fun_prop]
lemma poly_rawCcx_pair :
    Automatic.Poly (fun p : ℕ × ℕ × ℕ => rawCcx p.1 p.2.1 p.2.2) := by
  unfold rawCcx
  fun_prop

@[fun_prop]
lemma poly_rawCcx_comp {α : Type} [Automatic.Coding α] {a b c : α → ℕ}
    (ha : Automatic.Poly a) (hb : Automatic.Poly b) (hc : Automatic.Poly c) :
    Automatic.Poly (fun x => rawCcx (a x) (b x) (c x)) := by
  rcases ha with ⟨Pa⟩
  rcases hb with ⟨Pb⟩
  rcases hc with ⟨Pc⟩
  rcases poly_rawCcx_pair with ⟨Pr⟩
  exact ⟨((Pa.fanout (Pb.fanout Pc)).comp Pr).congr _ (fun _ => rfl)⟩

def rawSwap (a b : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(4, a, b), (4, b, a), (4, a, b)]

@[fun_prop]
lemma poly_rawSwap_comp {α : Type} [Automatic.Coding α] {a b : α → ℕ}
    (ha : Automatic.Poly a) (hb : Automatic.Poly b) :
    Automatic.Poly (fun x => rawSwap (a x) (b x)) := by
  unfold rawSwap
  fun_prop

def fuelVec (xs : List Bool) : List ℕ :=
  (true :: true :: xs).flatMap (fun _ =>
    (true :: true :: xs).flatMap (fun _ =>
      (true :: true :: xs).flatMap (fun _ => List.range 128)))

def fuelIdx (xs : List Bool) : List ℕ :=
  List.range (fuelVec xs).length

def rangeFuel (fuel : List ℕ) (n : ℕ) : List ℕ :=
  fuel.filter (fun i => decide (i < n))

def encNatFuel (fuel : List ℕ) (n : ℕ) : List Bool :=
  ((rangeFuel fuel n).map (fun _ => true)) ++ [false]

def encRawInstrFuel (fuel : List ℕ) (g : ℕ × ℕ × ℕ) : List Bool :=
  if g.1 = 4 then
    encNatFuel fuel g.1 ++ encNatFuel fuel g.2.1 ++ encNatFuel fuel g.2.2
  else
    encNatFuel fuel g.1 ++ encNatFuel fuel g.2.1

def encRawLayerFuel (fuel : List ℕ) (gs : List (ℕ × ℕ × ℕ)) : List Bool :=
  encNatFuel fuel gs.length ++ gs.flatMap (encRawInstrFuel fuel)

@[fun_prop] lemma poly_fuelIdx : Automatic.Poly fuelIdx := by unfold fuelIdx fuelVec; fun_prop
@[fun_prop] lemma poly_rangeFuel : Automatic.Poly (fun p : List ℕ × ℕ => rangeFuel p.1 p.2) := by
  unfold rangeFuel; fun_prop
@[fun_prop]
lemma poly_rangeFuel_comp {α : Type} [Automatic.Coding α] {fuel : α → List ℕ} {n : α → ℕ}
    (hf : Automatic.Poly fuel) (hn : Automatic.Poly n) :
    Automatic.Poly (fun x => rangeFuel (fuel x) (n x)) := by
  rcases hf with ⟨Pf⟩; rcases hn with ⟨Pn⟩
  rcases poly_rangeFuel with ⟨Pr⟩
  exact ⟨((Pf.fanout Pn).comp Pr).congr _ (fun _ => rfl)⟩
@[fun_prop] lemma poly_encNatFuel : Automatic.Poly (fun p : List ℕ × ℕ => encNatFuel p.1 p.2) := by
  unfold encNatFuel; fun_prop
@[fun_prop]
lemma poly_encNatFuel_comp {α : Type} [Automatic.Coding α] {fuel : α → List ℕ} {n : α → ℕ}
    (hf : Automatic.Poly fuel) (hn : Automatic.Poly n) :
    Automatic.Poly (fun x => encNatFuel (fuel x) (n x)) := by
  rcases hf with ⟨Pf⟩; rcases hn with ⟨Pn⟩
  rcases poly_encNatFuel with ⟨Pe⟩
  exact ⟨((Pf.fanout Pn).comp Pe).congr _ (fun _ => rfl)⟩
@[fun_prop] lemma poly_encRawInstrFuel :
    Automatic.Poly (fun p : List ℕ × (ℕ × ℕ × ℕ) => encRawInstrFuel p.1 p.2) := by
  unfold encRawInstrFuel; fun_prop
@[fun_prop] lemma poly_encRawLayerFuel :
    Automatic.Poly (fun p : List ℕ × List (ℕ × ℕ × ℕ) => encRawLayerFuel p.1 p.2) := by
  unfold encRawLayerFuel; fun_prop
@[fun_prop]
lemma poly_encRawLayerFuel_comp {α : Type} [Automatic.Coding α] {fuel : α → List ℕ}
    {gs : α → List (ℕ × ℕ × ℕ)} (hf : Automatic.Poly fuel) (hgs : Automatic.Poly gs) :
    Automatic.Poly (fun x => encRawLayerFuel (fuel x) (gs x)) := by
  rcases hf with ⟨Pf⟩; rcases hgs with ⟨Pgs⟩
  rcases poly_encRawLayerFuel with ⟨Pe⟩
  exact ⟨((Pf.fanout Pgs).comp Pe).congr _ (fun _ => rfl)⟩

def rawShiftUp (fuel : List ℕ) (W : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((rangeFuel fuel W).reverse).flatMap (fun k => rawSwap k (k + 1))

def rawShiftDown (fuel : List ℕ) (W : ℕ) : List (ℕ × ℕ × ℕ) :=
  (rangeFuel fuel W).flatMap (fun k => rawSwap k (k + 1))

def rawFlipCtrl (fuel : List ℕ) (L : ℕ) : List (ℕ × ℕ × ℕ) :=
  (rangeFuel fuel L).map (fun k => (3, 1 + L + k, 0))

def rawFlipCtrlRev (fuel : List ℕ) (L : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((rangeFuel fuel L).reverse).map (fun k => (3, 1 + L + k, 0))

def rawCascadeStep (W L k : ℕ) : List (ℕ × ℕ × ℕ) :=
  if k = 0 then rawCcx 1 (1 + L) (1 + W)
  else rawCcx (1 + W + (k - 1)) (1 + L + k) (1 + W + k)

@[fun_prop]
lemma poly_rawCascadeStep_pair :
    Automatic.Poly (fun p : ℕ × ℕ × ℕ => rawCascadeStep p.1 p.2.1 p.2.2) := by
  unfold rawCascadeStep
  fun_prop

@[fun_prop]
lemma poly_rawCascadeStep_comp {α : Type} [Automatic.Coding α] {W L k : α → ℕ}
    (hW : Automatic.Poly W) (hL : Automatic.Poly L) (hk : Automatic.Poly k) :
    Automatic.Poly (fun x => rawCascadeStep (W x) (L x) (k x)) := by
  rcases hW with ⟨PW⟩; rcases hL with ⟨PL⟩; rcases hk with ⟨Pk⟩
  rcases poly_rawCascadeStep_pair with ⟨Pr⟩
  exact ⟨((PW.fanout (PL.fanout Pk)).comp Pr).congr _ (fun _ => rfl)⟩

def rawCascade (fuel : List ℕ) (W L : ℕ) : List (ℕ × ℕ × ℕ) :=
  (rangeFuel fuel L).flatMap (fun k => rawCascadeStep W L k)

def rawCascadeRev (fuel : List ℕ) (W L : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((rangeFuel fuel L).reverse).flatMap (fun k => rawCascadeStep W L k)

def rawGammaMark (fuel : List ℕ) (W L : ℕ) : List (ℕ × ℕ × ℕ) :=
  rawShiftUp fuel W ++ rawFlipCtrl fuel L ++ rawCascade fuel W L ++
    [(1, 1 + W + (L - 1), 0), (1, 1 + W + (L - 1), 0)] ++
    [(4, 1, 0), (4, 1 + W + (L - 1), 0)] ++
    rawCascadeRev fuel W L ++ rawFlipCtrlRev fuel L

def rawGammaUnmark (fuel : List ℕ) (W L : ℕ) : List (ℕ × ℕ × ℕ) :=
  rawFlipCtrl fuel L ++ rawCascade fuel W L ++
    [(4, 1, 0), (4, 1 + W + (L - 1), 0)] ++
    rawCascadeRev fuel W L ++ rawFlipCtrlRev fuel L ++ rawShiftDown fuel W

@[fun_prop]
lemma poly_rawGammaMark :
    Automatic.Poly (fun p : List ℕ × ℕ × ℕ => rawGammaMark p.1 p.2.1 p.2.2) := by
  unfold rawGammaMark rawShiftUp rawFlipCtrl rawCascade rawCascadeRev rawFlipCtrlRev
  fun_prop

@[fun_prop]
lemma poly_rawGammaUnmark :
    Automatic.Poly (fun p : List ℕ × ℕ × ℕ => rawGammaUnmark p.1 p.2.1 p.2.2) := by
  unfold rawGammaUnmark rawShiftDown rawFlipCtrl rawCascade rawCascadeRev rawFlipCtrlRev
  fun_prop

def gammaMarkBuilder (xs : List Bool) : List Bool :=
  encNatFuel (fuelIdx xs) (gammaWRaw xs) ++
    encRawLayerFuel (fuelIdx xs) (rawGammaMark (fuelIdx xs) (tagWRaw xs) (labWRaw xs))

def gammaUnmarkBuilder (xs : List Bool) : List Bool :=
  encNatFuel (fuelIdx xs) (gammaWRaw xs) ++
    encRawLayerFuel (fuelIdx xs) (rawGammaUnmark (fuelIdx xs) (tagWRaw xs) (labWRaw xs))

lemma poly_gammaMarkBuilder : Automatic.Poly gammaMarkBuilder := by
  rcases poly_fuelIdx with ⟨Pf⟩
  rcases poly_gammaWRaw with ⟨Pg⟩
  rcases poly_tagWRaw with ⟨Pt⟩
  rcases poly_labWRaw with ⟨Pl⟩
  rcases poly_rawGammaMark with ⟨Prm⟩
  rcases poly_encNatFuel with ⟨Pen⟩
  rcases poly_encRawLayerFuel with ⟨Pel⟩
  rcases (Automatic.Poly.list_append : Automatic.Poly fun p : List Bool × List Bool => p.1 ++ p.2) with ⟨Pap⟩
  have P_mark : PolyProgram Automatic.enc Automatic.enc
      (fun xs => rawGammaMark (fuelIdx xs) (tagWRaw xs) (labWRaw xs)) :=
    ((Pf.fanout (Pt.fanout Pl)).comp Prm).congr _ (fun _ => by dsimp only [Function.comp_def])
  have P_part1 : PolyProgram Automatic.enc Automatic.enc
      (fun xs => encNatFuel (fuelIdx xs) (gammaWRaw xs)) :=
    ((Pf.fanout Pg).comp Pen).congr _ (fun _ => by dsimp only [Function.comp_def])
  have P_part2 : PolyProgram Automatic.enc Automatic.enc
      (fun xs => encRawLayerFuel (fuelIdx xs) (rawGammaMark (fuelIdx xs) (tagWRaw xs) (labWRaw xs))) :=
    ((Pf.fanout P_mark).comp Pel).congr _ (fun _ => by dsimp only [Function.comp_def])
  exact ⟨((P_part1.fanout P_part2).comp Pap).congr gammaMarkBuilder
    (fun _ => by unfold gammaMarkBuilder; dsimp only [Function.comp_def])⟩

lemma poly_gammaUnmarkBuilder : Automatic.Poly gammaUnmarkBuilder := by
  rcases poly_fuelIdx with ⟨Pf⟩
  rcases poly_gammaWRaw with ⟨Pg⟩
  rcases poly_tagWRaw with ⟨Pt⟩
  rcases poly_labWRaw with ⟨Pl⟩
  rcases poly_rawGammaUnmark with ⟨Prm⟩
  rcases poly_encNatFuel with ⟨Pen⟩
  rcases poly_encRawLayerFuel with ⟨Pel⟩
  rcases (Automatic.Poly.list_append : Automatic.Poly fun p : List Bool × List Bool => p.1 ++ p.2) with ⟨Pap⟩
  have P_unmark : PolyProgram Automatic.enc Automatic.enc
      (fun xs => rawGammaUnmark (fuelIdx xs) (tagWRaw xs) (labWRaw xs)) :=
    ((Pf.fanout (Pt.fanout Pl)).comp Prm).congr _ (fun _ => by dsimp only [Function.comp_def])
  have P_part1 : PolyProgram Automatic.enc Automatic.enc
      (fun xs => encNatFuel (fuelIdx xs) (gammaWRaw xs)) :=
    ((Pf.fanout Pg).comp Pen).congr _ (fun _ => by dsimp only [Function.comp_def])
  have P_part2 : PolyProgram Automatic.enc Automatic.enc
      (fun xs => encRawLayerFuel (fuelIdx xs) (rawGammaUnmark (fuelIdx xs) (tagWRaw xs) (labWRaw xs))) :=
    ((Pf.fanout P_unmark).comp Pel).congr _ (fun _ => by dsimp only [Function.comp_def])
  exact ⟨((P_part1.fanout P_part2).comp Pap).congr gammaUnmarkBuilder
    (fun _ => by unfold gammaUnmarkBuilder; dsimp only [Function.comp_def])⟩

lemma polyTime_of_automatic_str {f : Str → Str} (hf : Automatic.Poly f) :
    PolyTimeComputable f := by
  rcases hf with ⟨P⟩
  exact ⟨((BooleanLists.packProgram.comp P).comp BooleanLists.unpackProgram).stock⟩

lemma mapCirc_toRawInstr {n : ℕ} (e : Fin 3 ↪ Fin n) (c : List (Instr 3)) :
    (mapCirc e c).map toRawInstr =
      (c.map toRawInstr).map (fun g =>
        (g.1,
         if g.2.1 = 0 then (e 0).val else if g.2.1 = 1 then (e 1).val else (e 2).val,
         if g.1 = 4 then (if g.2.2 = 0 then (e 0).val else if g.2.2 = 1 then (e 1).val else (e 2).val) else 0)) := by
  induction c with
  | nil => rfl
  | cons g gs ih =>
    change toRawInstr (mapInstr e g) :: (mapCirc e gs).map toRawInstr = _ :: _
    rw [ih]
    congr 1
    cases g with
    | h i => fin_cases i <;> rfl
    | s i => fin_cases i <;> rfl
    | t i => fin_cases i <;> rfl
    | x i => fin_cases i <;> rfl
    | cnot i j _ => fin_cases i <;> fin_cases j <;> rfl

lemma compileRev_ccx_toRawInstr {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((RevGate.ccx i j k hij hik hjk).compile).map toRawInstr = rawCcx i.val j.val k.val := by
  simp only [RevGate.compile, mapCirc_toRawInstr, rawCcx, rawCcx3, wire3_0, wire3_1, wire3_2]

lemma compileRev_append_toRawInstr {n : ℕ} (gs hs : List (RevGate n)) :
    (compileRev (gs ++ hs)).map toRawInstr =
      (compileRev gs).map toRawInstr ++ (compileRev hs).map toRawInstr := by
  simp [compileRev_append]

lemma shiftUpAux_toRawInstr {W N : ℕ} (hWN : W < N) (k : ℕ) (hk : k ≤ W) :
    (compileRev (shiftUpAux hWN k hk)).map toRawInstr =
      ((List.range k).reverse).flatMap (fun m => rawSwap m (m + 1)) := by
  induction k with
  | zero => simp [shiftUpAux, compileRev]
  | succ k ih =>
    simp only [shiftUpAux, compileRev_append_toRawInstr, List.range_succ,
      List.reverse_append, List.reverse_singleton, List.singleton_append, List.flatMap_cons]
    rw [ih (by omega)]
    congr 1

lemma shiftUpAux_rev_toRawInstr {W N : ℕ} (hWN : W < N) (k : ℕ) (hk : k ≤ W) :
    (compileRev (shiftUpAux hWN k hk).reverse).map toRawInstr =
      (List.range k).flatMap (fun m => rawSwap m (m + 1)) := by
  induction k with
  | zero => simp [shiftUpAux, compileRev]
  | succ k ih =>
    simp only [shiftUpAux, List.reverse_append, compileRev_append_toRawInstr,
      List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [ih (by omega)]
    congr 1

lemma flipCtrlAux_toRawInstr (D : FieldData) (k : ℕ) (hk : k ≤ D.labW) :
    (compileRev (flipCtrlAux D k hk)).map toRawInstr =
      (List.range k).map (fun m => (3, 1 + D.labW + m, 0)) := by
  induction k with
  | zero => simp [flipCtrlAux, compileRev]
  | succ k ih =>
    simp only [flipCtrlAux, compileRev_append_toRawInstr, List.range_succ, List.map_append,
      List.map_singleton]
    rw [ih (by omega)]
    congr 1

lemma compileRev_singleton {n : ℕ} (g : RevGate n) :
    compileRev [g] = g.compile := by
  simp [compileRev]

lemma flipCtrlAux_rev_toRawInstr (D : FieldData) (k : ℕ) (hk : k ≤ D.labW) :
    (compileRev (flipCtrlAux D k hk).reverse).map toRawInstr =
      ((List.range k).reverse).map (fun m => (3, 1 + D.labW + m, 0)) := by
  induction k with
  | zero => simp [flipCtrlAux, compileRev]
  | succ k ih =>
    rw [show (flipCtrlAux D (k + 1) hk).reverse =
      [RevGate.x (ctrlWire D k hk)] ++ (flipCtrlAux D k (by omega)).reverse from by
      simp [flipCtrlAux, List.reverse_append]]
    rw [compileRev_append_toRawInstr, ih (by omega)]
    simp [List.range_succ, List.reverse_append, compileRev_singleton, RevGate.compile, toRawInstr, ctrlWire]

lemma cascadeAux_toRawInstr (D : FieldData) (k : ℕ) (hk : k ≤ D.labW) :
    (compileRev (cascadeAux D k hk)).map toRawInstr =
      (List.range k).flatMap (fun m => rawCascadeStep ((D.r + 1) * D.labW) D.labW m) := by
  induction k with
  | zero => simp [cascadeAux, compileRev]
  | succ k ih =>
    cases k with
    | zero =>
      simp only [cascadeAux, compileRev_singleton, List.range_succ, List.range_zero, List.nil_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have h1 := compileRev_ccx_toRawInstr (flagWire D) (ctrlWire D 0 hk) (ancWire D 0 hk)
        (by simp [Fin.ext_iff, flagWire, ctrlWire]; have := two_le_labW D; omega)
        (by simp [Fin.ext_iff, flagWire, ancWire]; have := two_mul_labW_le_tagW D; have := two_le_labW D; omega)
        (by simp [Fin.ext_iff, ctrlWire, ancWire]; have := two_mul_labW_le_tagW D; omega)
      simpa [rawCascadeStep, flagWire, ctrlWire, ancWire] using h1
    | succ k =>
      simp only [cascadeAux, compileRev_append_toRawInstr]
      rw [ih (by omega), compileRev_singleton]
      have hccx := compileRev_ccx_toRawInstr (ancWire D k (by omega)) (ctrlWire D (k + 1) hk) (ancWire D (k + 1) hk)
        (by simp [Fin.ext_iff, ancWire, ctrlWire]; have := two_mul_labW_le_tagW D; omega)
        (by simp [Fin.ext_iff, ancWire])
        (by simp [Fin.ext_iff, ctrlWire, ancWire]; have := two_mul_labW_le_tagW D; omega)
      rw [hccx]
      conv_rhs => rw [List.range_succ, List.flatMap_append]
      simp [rawCascadeStep, ancWire, ctrlWire]

lemma cascadeAux_rev_toRawInstr (D : FieldData) (k : ℕ) (hk : k ≤ D.labW) :
    (compileRev (cascadeAux D k hk).reverse).map toRawInstr =
      ((List.range k).reverse).flatMap (fun m => rawCascadeStep ((D.r + 1) * D.labW) D.labW m) := by
  induction k with
  | zero => simp [cascadeAux, compileRev]
  | succ k ih =>
    cases k with
    | zero =>
      simp only [cascadeAux, List.reverse_singleton, compileRev_singleton, List.range_succ, List.range_zero,
        List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have h1 := compileRev_ccx_toRawInstr (flagWire D) (ctrlWire D 0 hk) (ancWire D 0 hk)
        (by simp [Fin.ext_iff, flagWire, ctrlWire]; have := two_le_labW D; omega)
        (by simp [Fin.ext_iff, flagWire, ancWire]; have := two_mul_labW_le_tagW D; have := two_le_labW D; omega)
        (by simp [Fin.ext_iff, ctrlWire, ancWire]; have := two_mul_labW_le_tagW D; omega)
      simpa [rawCascadeStep, flagWire, ctrlWire, ancWire] using h1
    | succ k =>
      rw [show (cascadeAux D (k + 2) hk).reverse =
        [RevGate.ccx (ancWire D k (by omega)) (ctrlWire D (k + 1) hk) (ancWire D (k + 1) hk)
          (by simp [Fin.ext_iff, ancWire, ctrlWire]; have := two_mul_labW_le_tagW D; omega)
          (by simp [Fin.ext_iff, ancWire])
          (by simp [Fin.ext_iff, ctrlWire, ancWire]; have := two_mul_labW_le_tagW D; omega)] ++
          (cascadeAux D (k + 1) (by omega)).reverse from by
        simp [cascadeAux, List.reverse_append]]
      rw [compileRev_append_toRawInstr, ih (by omega), compileRev_singleton]
      have hccx := compileRev_ccx_toRawInstr (ancWire D k (by omega)) (ctrlWire D (k + 1) hk) (ancWire D (k + 1) hk)
        (by simp [Fin.ext_iff, ancWire, ctrlWire]; have := two_mul_labW_le_tagW D; omega)
        (by simp [Fin.ext_iff, ancWire])
        (by simp [Fin.ext_iff, ctrlWire, ancWire]; have := two_mul_labW_le_tagW D; omega)
      rw [hccx]
      simp [rawCascadeStep, ancWire, ctrlWire, List.range_succ, List.reverse_append]

lemma fuelVec_length (xs : List Bool) :
    (fuelVec xs).length = 128 * (xs.length + 2) ^ 3 := by
  unfold fuelVec
  have h1 : ∀ {α β : Type} (l : List α) (f : α → List β) (k : ℕ),
      (∀ a ∈ l, (f a).length = k) → (l.flatMap f).length = l.length * k := by
    intro α β l f k hk
    induction l with
    | nil => simp
    | cons a tl ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        hk a List.mem_cons_self, ih (fun b hb => hk b (List.mem_cons_of_mem _ hb))]
      ring
  rw [h1 _ _ (128 * (xs.length + 2) ^ 2)]
  · simp; ring
  · intro _ _
    rw [h1 _ _ (128 * (xs.length + 2))]
    · simp; ring
    · intro _ _
      rw [h1 _ _ 128 (fun _ _ => by simp)]
      simp; ring

lemma encNatFuel_eq {F n : ℕ} (hn : n ≤ F) :
    encNatFuel (List.range F) n = encNat n := by
  unfold encNatFuel rangeFuel encNat
  rw [filter_range_lt_eq hn]
  have hrep : (List.range n).map (fun _ => true) = List.replicate n true := by
    apply List.ext_getElem <;> simp
  rw [hrep]

lemma encRawInstrFuel_eq {F m : ℕ} (h4 : 4 ≤ F) (hm : m ≤ F) (g : Instr m) :
    encRawInstrFuel (List.range F) (toRawInstr g) = encInstr g := by
  cases g with
  | h i =>
    simp [toRawInstr, encRawInstrFuel, encInstr, encNatFuel_eq (by omega : 0 ≤ F),
      encNatFuel_eq (by omega : i.val ≤ F)]
  | s i =>
    simp [toRawInstr, encRawInstrFuel, encInstr, encNatFuel_eq (by omega : 1 ≤ F),
      encNatFuel_eq (by omega : i.val ≤ F)]
  | t i =>
    simp [toRawInstr, encRawInstrFuel, encInstr, encNatFuel_eq (by omega : 2 ≤ F),
      encNatFuel_eq (by omega : i.val ≤ F)]
  | x i =>
    simp [toRawInstr, encRawInstrFuel, encInstr, encNatFuel_eq (by omega : 3 ≤ F),
      encNatFuel_eq (by omega : i.val ≤ F)]
  | cnot i j _ =>
    simp [toRawInstr, encRawInstrFuel, encInstr, encNatFuel_eq h4,
      encNatFuel_eq (by omega : i.val ≤ F), encNatFuel_eq (by omega : j.val ≤ F)]

lemma encRawLayerFuel_eq {F m : ℕ} (h4 : 4 ≤ F) (hm : m ≤ F) (c : List (Instr m)) (hc : c.length ≤ F) :
    encRawLayerFuel (List.range F) (c.map toRawInstr) = encLayer c := by
  unfold encRawLayerFuel encLayer encStr
  simp only [List.length_map]
  rw [encNatFuel_eq hc, List.flatMap_map]
  congr 1
  induction c with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.map_cons, List.flatten_cons, encRawInstrFuel_eq h4 hm g,
      ih (by simp at hc; omega)]

lemma ccx3_length_eq : ccx3.length = 24 := by
  decide

lemma compileRev_ccx_length {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((RevGate.ccx i j k hij hik hjk).compile).length = 24 := by
  simp [RevGate.compile, mapCirc, ccx3_length_eq]

lemma shiftUpAux_length {W N : ℕ} (hWN : W < N) (k : ℕ) (hk : k ≤ W) :
    (compileRev (shiftUpAux hWN k hk)).length = 3 * k := by
  induction k with
  | zero => simp [shiftUpAux, compileRev]
  | succ k ih =>
    simp only [shiftUpAux, compileRev_append, List.length_append, ih (by omega)]
    have hsw : (compileRev (swapRev (⟨k, by omega⟩ : Fin N) (⟨k + 1, by omega⟩ : Fin N) (by simp [Fin.ext_iff]))).length = 3 := by
      simp [swapRev, compileRev, RevGate.compile]
    rw [hsw]; ring

lemma flipCtrlAux_length (D : FieldData) (k : ℕ) (hk : k ≤ D.labW) :
    (compileRev (flipCtrlAux D k hk)).length = k := by
  induction k with
  | zero => simp [flipCtrlAux, compileRev]
  | succ k ih =>
    simp only [flipCtrlAux, compileRev_append, List.length_append, ih (by omega)]
    simp [compileRev, RevGate.compile]

lemma cascadeAux_length (D : FieldData) (k : ℕ) (hk : k ≤ D.labW) :
    (compileRev (cascadeAux D k hk)).length = 24 * k := by
  induction k with
  | zero => simp [cascadeAux, compileRev]
  | succ k ih =>
    cases k with
    | zero =>
      simp only [cascadeAux, compileRev, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact compileRev_ccx_length (flagWire D) (ctrlWire D 0 hk) (ancWire D 0 hk)
        (by simp [Fin.ext_iff, flagWire, ctrlWire]; have := two_le_labW D; omega)
        (by simp [Fin.ext_iff, flagWire, ancWire]; have := two_mul_labW_le_tagW D; have := two_le_labW D; omega)
        (by simp [Fin.ext_iff, ctrlWire, ancWire]; have := two_mul_labW_le_tagW D; omega)
    | succ k =>
      simp only [cascadeAux, compileRev_append, List.length_append, ih (by omega)]
      have h1 : (compileRev [.ccx (ancWire D k (by omega)) (ctrlWire D (k + 1) hk) (ancWire D (k + 1) hk)
          (by simp [Fin.ext_iff, ancWire, ctrlWire]; have := two_mul_labW_le_tagW D; omega)
          (by simp [Fin.ext_iff, ancWire])
          (by simp [Fin.ext_iff, ctrlWire, ancWire]; have := two_mul_labW_le_tagW D; omega)]).length = 24 := by
        simp only [compileRev, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact compileRev_ccx_length _ _ _ _ _ _
      rw [h1]; ring

lemma compileRev_reverse_length {n : ℕ} (gs : List (RevGate n)) :
    (compileRev gs.reverse).length = (compileRev gs).length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [compileRev, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.length_append] at *
    omega

lemma gammaMarkCirc_length (D : FieldData) :
    (gammaMarkCirc D).length = 3 * ((D.r + 1) * D.labW) + 50 * D.labW + 4 := by
  have h0 : 0 < gammaW D := by have := gammaW_gt_tagW D; omega
  have hL : D.labW - 1 < D.labW := by have := two_le_labW D; omega
  have hcopy : (compileRev ([RevGate.cnot (flagWire D) ⟨0, h0⟩ (by simp [Fin.ext_iff, flagWire]),
      RevGate.cnot (ancWire D (D.labW - 1) hL) ⟨0, h0⟩ (by simp [Fin.ext_iff, ancWire])] : List (RevGate (gammaW D)))).length = 2 := by
    simp [compileRev, RevGate.compile]
  unfold gammaMarkCirc
  simp only [List.length_append, compileRev_append, List.length_cons, List.length_nil]
  rw [shiftUp, shiftUpAux_length, compileRev_reverse_length]
  simp only [prepZero, compileRev_append, List.length_append]
  rw [flipCtrlAux_length, cascadeAux_length, hcopy]
  ring

lemma gammaUnmarkCirc_length (D : FieldData) :
    (gammaUnmarkCirc D).length = 3 * ((D.r + 1) * D.labW) + 50 * D.labW + 2 := by
  have h0 : 0 < gammaW D := by have := gammaW_gt_tagW D; omega
  have hL : D.labW - 1 < D.labW := by have := two_le_labW D; omega
  have hcopy : (compileRev ([RevGate.cnot (flagWire D) ⟨0, h0⟩ (by simp [Fin.ext_iff, flagWire]),
      RevGate.cnot (ancWire D (D.labW - 1) hL) ⟨0, h0⟩ (by simp [Fin.ext_iff, ancWire])] : List (RevGate (gammaW D)))).length = 2 := by
    simp [compileRev, RevGate.compile]
  unfold gammaUnmarkCirc
  simp only [compileRev_append, List.length_append]
  rw [compileRev_reverse_length, compileRev_reverse_length, shiftUp, shiftUpAux_length]
  simp only [prepZero, compileRev_append, List.length_append]
  rw [flipCtrlAux_length, cascadeAux_length, hcopy]
  ring

lemma labW_le_two_encData_sq (D : FieldData) :
    D.labW ≤ 2 * D.encData.length ^ 2 := by
  have hp : D.p < 2 ^ D.p.bits.length := natBits_length_le_iff.mp le_rfl
  have hq : D.q < 2 ^ (D.p.bits.length * D.r) := by
    change D.p ^ D.r < 2 ^ (D.p.bits.length * D.r)
    rw [Nat.pow_mul]
    exact Nat.pow_lt_pow_left hp (by have := D.hr; omega)
  have hq2 : D.q ^ 2 < 2 ^ (2 * D.p.bits.length * D.r) := by
    calc D.q ^ 2 = D.q * D.q := sq D.q
      _ < 2 ^ (D.p.bits.length * D.r) * 2 ^ (D.p.bits.length * D.r) := Nat.mul_lt_mul_of_lt_of_lt hq hq
      _ = 2 ^ (2 * D.p.bits.length * D.r) := by rw [← Nat.pow_add]; ring_nf
  have hclog : D.labW ≤ 2 * D.p.bits.length * D.r := by
    unfold FieldData.labW
    rw [Nat.clog_le_iff_le_pow (by decide)]
    exact le_of_lt hq2
  have hp_len := encData_length_ge_p_bits D
  have hr_len := encData_length_ge_r D
  nlinarith

lemma gamma_fuel_sufficient (D : FieldData) (k : ℕ) :
    let F := (fuelVec (D.encData ++ encNat k)).length
    4 ≤ F ∧ gammaW D ≤ F ∧ (gammaMarkCirc D).length ≤ F ∧ (gammaUnmarkCirc D).length ≤ F := by
  intro F
  have hF : F = 128 * ((D.encData ++ encNat k).length + 2) ^ 3 := fuelVec_length _
  set N := (D.encData ++ encNat k).length
  have hN_ge_enc : D.encData.length ≤ N := by simp [N]
  have hL : D.labW ≤ 2 * (N + 2) ^ 2 := by
    have h1 := labW_le_two_encData_sq D
    nlinarith
  have hr : D.r + 1 ≤ N + 2 := by
    have h1 := encData_length_ge_r D
    omega
  have hW : (D.r + 1) * D.labW ≤ 2 * (N + 2) ^ 3 := by
    nlinarith
  have hN2 : 1 ≤ N + 2 := by omega
  have hpow1 : 1 ≤ (N + 2) ^ 3 := Nat.one_le_pow 3 (N + 2) hN2
  have hL3 : D.labW ≤ 2 * (N + 2) ^ 3 := by nlinarith
  have hmark : (gammaMarkCirc D).length ≤ 128 * (N + 2) ^ 3 := by
    rw [gammaMarkCirc_length]
    omega
  have hunmark : (gammaUnmarkCirc D).length ≤ 128 * (N + 2) ^ 3 := by
    rw [gammaUnmarkCirc_length]
    omega
  have hgam : gammaW D ≤ 128 * (N + 2) ^ 3 := by
    unfold gammaW
    omega
  have h4 : 4 ≤ 128 * (N + 2) ^ 3 := by omega
  rw [hF]
  exact ⟨h4, hgam, hmark, hunmark⟩

lemma gammaMarkCirc_toRawInstr (D : FieldData) (F : ℕ) (hF_W : (D.r + 1) * D.labW ≤ F) (hF_L : D.labW ≤ F) :
    (gammaMarkCirc D).map toRawInstr =
      rawGammaMark (List.range F) ((D.r + 1) * D.labW) D.labW := by
  have h0 : 0 < gammaW D := by have := gammaW_gt_tagW D; omega
  have hL : D.labW - 1 < D.labW := by have := two_le_labW D; omega
  have hmark : gammaMarkCirc D =
      compileRev (shiftUp D) ++ compileRev (flipCtrlAux D D.labW le_rfl) ++
        compileRev (cascadeAux D D.labW le_rfl) ++
        [.s (ancWire D (D.labW - 1) hL), .s (ancWire D (D.labW - 1) hL)] ++
        compileRev [.cnot (flagWire D) ⟨0, h0⟩ (by simp [Fin.ext_iff, flagWire]),
          .cnot (ancWire D (D.labW - 1) hL) ⟨0, h0⟩ (by simp [Fin.ext_iff, ancWire])] ++
        compileRev (cascadeAux D D.labW le_rfl).reverse ++
        compileRev (flipCtrlAux D D.labW le_rfl).reverse := by
    unfold gammaMarkCirc
    simp only [prepZero, List.reverse_append, compileRev_append, List.append_assoc]
  rw [hmark]
  simp only [List.map_append]
  unfold rawGammaMark rawShiftUp rawFlipCtrl rawCascade rawCascadeRev rawFlipCtrlRev rangeFuel
  rw [filter_range_lt_eq hF_W, filter_range_lt_eq hF_L]
  rw [shiftUp, shiftUpAux_toRawInstr, flipCtrlAux_toRawInstr, cascadeAux_toRawInstr,
    cascadeAux_rev_toRawInstr, flipCtrlAux_rev_toRawInstr]
  simp [compileRev, RevGate.compile, toRawInstr, flagWire, ancWire]

lemma gammaUnmarkCirc_toRawInstr (D : FieldData) (F : ℕ) (hF_W : (D.r + 1) * D.labW ≤ F) (hF_L : D.labW ≤ F) :
    (gammaUnmarkCirc D).map toRawInstr =
      rawGammaUnmark (List.range F) ((D.r + 1) * D.labW) D.labW := by
  have h0 : 0 < gammaW D := by have := gammaW_gt_tagW D; omega
  have hL : D.labW - 1 < D.labW := by have := two_le_labW D; omega
  have hunmark : gammaUnmarkCirc D =
      compileRev (flipCtrlAux D D.labW le_rfl) ++ compileRev (cascadeAux D D.labW le_rfl) ++
        compileRev [.cnot (flagWire D) ⟨0, h0⟩ (by simp [Fin.ext_iff, flagWire]),
          .cnot (ancWire D (D.labW - 1) hL) ⟨0, h0⟩ (by simp [Fin.ext_iff, ancWire])] ++
        compileRev (cascadeAux D D.labW le_rfl).reverse ++
        compileRev (flipCtrlAux D D.labW le_rfl).reverse ++
        compileRev (shiftUp D).reverse := by
    unfold gammaUnmarkCirc
    simp only [prepZero, List.reverse_append, compileRev_append, List.append_assoc]
  rw [hunmark]
  simp only [List.map_append]
  unfold rawGammaUnmark rawShiftDown rawFlipCtrl rawCascade rawCascadeRev rawFlipCtrlRev rangeFuel
  rw [filter_range_lt_eq hF_W, filter_range_lt_eq hF_L]
  rw [shiftUp, shiftUpAux_rev_toRawInstr, flipCtrlAux_toRawInstr, cascadeAux_toRawInstr,
    cascadeAux_rev_toRawInstr, flipCtrlAux_rev_toRawInstr]
  simp [compileRev, RevGate.compile, toRawInstr, flagWire, ancWire]

lemma gammaMarkBuilder_eq (D : FieldData) (k : ℕ) :
    gammaMarkBuilder (D.encData ++ encNat k) =
      encNat (gammaW D) ++ encLayer (gammaMarkCirc D) := by
  obtain ⟨h4, hgam, hmark, _⟩ := gamma_fuel_sufficient D k
  have hW : (D.r + 1) * D.labW ≤ (fuelVec (D.encData ++ encNat k)).length := by
    have : (D.r + 1) * D.labW ≤ gammaW D := by unfold gammaW; omega
    omega
  have hL : D.labW ≤ (fuelVec (D.encData ++ encNat k)).length := by
    have : D.labW ≤ gammaW D := by unfold gammaW; omega
    omega
  unfold gammaMarkBuilder
  rw [gammaWRaw_encData, tagWRaw_encData, labWRaw_encData]
  rw [show fuelIdx (D.encData ++ encNat k) = List.range (fuelVec (D.encData ++ encNat k)).length from rfl]
  rw [encNatFuel_eq hgam, ← gammaMarkCirc_toRawInstr D _ hW hL, encRawLayerFuel_eq h4 hgam _ hmark]

lemma gammaUnmarkBuilder_eq (D : FieldData) (k : ℕ) :
    gammaUnmarkBuilder (D.encData ++ encNat k) =
      encNat (gammaW D) ++ encLayer (gammaUnmarkCirc D) := by
  obtain ⟨h4, hgam, _, hunmark⟩ := gamma_fuel_sufficient D k
  have hW : (D.r + 1) * D.labW ≤ (fuelVec (D.encData ++ encNat k)).length := by
    have : (D.r + 1) * D.labW ≤ gammaW D := by unfold gammaW; omega
    omega
  have hL : D.labW ≤ (fuelVec (D.encData ++ encNat k)).length := by
    have : D.labW ≤ gammaW D := by unfold gammaW; omega
    omega
  unfold gammaUnmarkBuilder
  rw [gammaWRaw_encData, tagWRaw_encData, labWRaw_encData]
  rw [show fuelIdx (D.encData ++ encNat k) = List.range (fuelVec (D.encData ++ encNat k)).length from rfl]
  rw [encNatFuel_eq hgam, ← gammaUnmarkCirc_toRawInstr D _ hW hL, encRawLayerFuel_eq h4 hgam _ hunmark]

lemma r_le_log2_q (D : FieldData) : D.r ≤ Nat.log 2 D.q := by
  have hp2 : 2 ≤ D.p := D.hp.two_le
  have hpow : 2 ^ D.r ≤ D.q := by
    change 2 ^ D.r ≤ D.p ^ D.r
    exact Nat.pow_le_pow_left hp2 D.r
  have hq0 : D.q ≠ 0 := by have := D.one_lt_q; omega
  rw [← Nat.log2_eq_log_two, Nat.le_log2 hq0]
  exact hpow

lemma labW_le_two_log2_q_add_two (D : FieldData) : D.labW ≤ 2 * Nat.log 2 D.q + 2 := by
  unfold FieldData.labW
  rw [Nat.clog_le_iff_le_pow (by decide)]
  have hq : D.q < 2 ^ (Nat.log 2 D.q + 1) := Nat.lt_pow_succ_log_self (by decide) D.q
  have hq2 : D.q ^ 2 < 2 ^ (2 * Nat.log 2 D.q + 2) := by
    calc D.q ^ 2 = D.q * D.q := sq D.q
      _ < 2 ^ (Nat.log 2 D.q + 1) * 2 ^ (Nat.log 2 D.q + 1) := Nat.mul_lt_mul_of_lt_of_lt hq hq
      _ = 2 ^ (2 * Nat.log 2 D.q + 2) := by rw [← Nat.pow_add]; ring_nf
  exact le_of_lt hq2

lemma gammaMarkCirc_length_bound (D : FieldData) (k : ℕ) :
    (gammaMarkCirc D).length ≤ 60 * (Nat.log 2 D.q + k + 2) ^ 60 := by
  set B := Nat.log 2 D.q + k + 2
  have hB : 2 ≤ B := by omega
  have hr : D.r + 1 ≤ B := by have := r_le_log2_q D; omega
  have hL : D.labW ≤ 2 * B := by have := labW_le_two_log2_q_add_two D; omega
  have hW : (D.r + 1) * D.labW ≤ 2 * B ^ 2 := by nlinarith
  have h1 : 3 * ((D.r + 1) * D.labW) + 50 * D.labW + 4 ≤ 60 * B ^ 2 := by nlinarith
  have hpow : B ^ 2 ≤ B ^ 60 := Nat.pow_le_pow_right (by omega) (by decide)
  rw [gammaMarkCirc_length]
  nlinarith

lemma gammaUnmarkCirc_length_bound (D : FieldData) (k : ℕ) :
    (gammaUnmarkCirc D).length ≤ 60 * (Nat.log 2 D.q + k + 2) ^ 60 := by
  have h : (gammaUnmarkCirc D).length ≤ (gammaMarkCirc D).length := by
    rw [gammaUnmarkCirc_length, gammaMarkCirc_length]; omega
  exact h.trans (gammaMarkCirc_length_bound D k)

end PolyTimeSection

end GL2QFT_GammaMark_Aux

open GL2QFT GL2QFT.Circuits in
theorem solution :
    UniformlyImplementsOn (fun _ => True)
      (fun D c => D.tagCode (D.xEmb c))
      (fun D c => gammaTaggedCode D c)
      (fun D => Matrix.diagonal fun c => match c with | none => 1 | some α => if α = 0 then -1 else 1) ∧
    UniformlyImplementsOn (fun _ => True)
      (fun D c => gammaTaggedCode D c)
      (fun D c => D.tagCode (D.xEmb c))
      (fun _ => 1) := by
  refine ⟨?_, ?_⟩
  · refine ⟨fun D _ => GL2QFT_GammaMark_Aux.gammaW D,
      fun D _ => GL2QFT_GammaMark_Aux.gammaMarkCirc D,
      GL2QFT_GammaMark_Aux.gammaMarkBuilder, 60, ?_, ?_, ?_, ?_⟩
    · exact GL2QFT_GammaMark_Aux.polyTime_of_automatic_str GL2QFT_GammaMark_Aux.poly_gammaMarkBuilder
    · intro D _ k
      exact GL2QFT_GammaMark_Aux.gammaMarkBuilder_eq D k
    · intro D _ k
      exact GL2QFT_GammaMark_Aux.gammaMarkCirc_length_bound D k
    · intro D _ k
      refine ⟨?_, ?_, ?_⟩
      · dsimp only; unfold GL2QFT_GammaMark_Aux.gammaW; omega
      · dsimp only; unfold GL2QFT_GammaMark_Aux.gammaW
        have := GL2QFT_GammaMark_Aux.two_le_labW D
        omega
      · exact GL2QFT_GammaMark_Aux.gammaMarkCirc_implements D ((1 / 2 : ℝ) ^ k) (by positivity)
  · refine ⟨fun D _ => GL2QFT_GammaMark_Aux.gammaW D,
      fun D _ => GL2QFT_GammaMark_Aux.gammaUnmarkCirc D,
      GL2QFT_GammaMark_Aux.gammaUnmarkBuilder, 60, ?_, ?_, ?_, ?_⟩
    · exact GL2QFT_GammaMark_Aux.polyTime_of_automatic_str GL2QFT_GammaMark_Aux.poly_gammaUnmarkBuilder
    · intro D _ k
      exact GL2QFT_GammaMark_Aux.gammaUnmarkBuilder_eq D k
    · intro D _ k
      exact GL2QFT_GammaMark_Aux.gammaUnmarkCirc_length_bound D k
    · intro D _ k
      refine ⟨?_, ?_, ?_⟩
      · dsimp only; unfold GL2QFT_GammaMark_Aux.gammaW
        have := GL2QFT_GammaMark_Aux.two_le_labW D
        omega
      · dsimp only; unfold GL2QFT_GammaMark_Aux.gammaW; omega
      · exact GL2QFT_GammaMark_Aux.gammaUnmarkCirc_implements D ((1 / 2 : ℝ) ^ k) (by positivity)
