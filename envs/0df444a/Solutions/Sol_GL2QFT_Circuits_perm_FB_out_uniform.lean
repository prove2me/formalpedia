-- Prove2me | solution 1 for GL2QFT.Circuits.perm_FB_out_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T09:03:53.469349+00:00
-- url     : https://prove2.me/submissions/c36e53eb-1b19-4696-b9da-112052bbd182

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

set_option autoImplicit false

noncomputable section

open Classical

namespace GL2QFT_FBOut_Aux

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
  have hq := congrArg (fun v : EuclideanSpace ℂ ι => (WithLp.ofLp v) y) (h q)
  simpa [act_ket] using hq

lemma act_mul {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  apply WithLp.ofLp_injective
  funext y
  simp [act, Matrix.mulVec_mulVec]

lemma act_permMat {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ι) (q : ι) :
    act (permMat f) (ket q) = ket (f q) := by
  apply WithLp.ofLp_injective
  funext y
  simp only [act_ket, WithLp.ofLp_toLp, ket_apply, permMat, Matrix.of_apply]

lemma circUnitary_nil {n : ℕ} : circUnitary ([] : List (Instr n)) = 1 := by
  simp [circUnitary, Circuit.unitary]

lemma circUnitary_append {n : ℕ} (c₁ c₂ : List (Instr n)) :
    circUnitary (c₁ ++ c₂) = circUnitary c₂ * circUnitary c₁ := by
  simp [circUnitary, Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma embedOp_wire1 {n : ℕ} (M : Matrix Bool Bool ℂ) (i : Fin n) (y z : Qubits n) :
    embedOp (Gate.ofMatrix1 M).mat (wire1 i) y z =
      if ∀ a : Fin n, a ≠ i → y a = z a then M (y i) (z i) else 0 := by
  unfold embedOp Gate.ofMatrix1
  rw [Matrix.of_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range (wire1 i) → y a = z a) ↔
      ∀ a : Fin n, a ≠ i → y a = z a := by
    constructor
    · intro h a hai; exact h a (by rintro ⟨x, rfl⟩; exact hai rfl)
    · intro h a ha; exact h a (fun heq => ha ⟨0, by simp [heq]⟩)
  by_cases h1 : ∀ a : Fin n, a ≠ i → y a = z a
  · rw [if_pos (hiff.mpr h1), if_pos h1]
    rfl
  · rw [if_neg (fun hc => h1 (hiff.mp hc)), if_neg h1]

lemma embedOp_wire2 {n : ℕ} (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) (i j : Fin n) (hij : i ≠ j)
    (y z : Qubits n) :
    embedOp (Gate.ofMatrix2 M).mat (wire2 i j hij) y z =
      if ∀ a : Fin n, a ≠ i → a ≠ j → y a = z a then M (y i, y j) (z i, z j) else 0 := by
  unfold embedOp Gate.ofMatrix2
  rw [Matrix.of_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range (wire2 i j hij) → y a = z a) ↔
      ∀ a : Fin n, a ≠ i → a ≠ j → y a = z a := by
    constructor
    · intro h a hai haj
      apply h a
      rintro ⟨x, rfl⟩
      fin_cases x
      · exact hai rfl
      · exact haj rfl
    · intro h a ha
      exact h a (fun heq => ha ⟨0, by simp [heq]⟩) (fun heq => ha ⟨1, by simp [heq]⟩)
  by_cases h1 : ∀ a : Fin n, a ≠ i → a ≠ j → y a = z a
  · rw [if_pos (hiff.mpr h1), if_pos h1]
    rfl
  · rw [if_neg (fun hc => h1 (hiff.mp hc)), if_neg h1]

lemma instr_x_unitary {n : ℕ} (i : Fin n) :
    circUnitary [.x i] = permMat (fun q : Qubits n => Function.update q i (!q i)) := by
  ext y z
  simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one, instrApp]
  rw [embedOp_wire1]
  simp only [pauliX, Matrix.of_apply, permMat]
  by_cases hy : y = Function.update z i (!z i)
  · subst hy
    rw [if_pos rfl, if_pos (fun a hai => by simp [hai])]
    cases hzi : z i <;> simp
  · rw [if_neg hy]
    by_cases h1 : ∀ a : Fin n, a ≠ i → y a = z a
    · rw [if_pos h1]
      have hne : y i ≠ !z i := by
        intro heq
        apply hy
        funext a
        by_cases hai : a = i
        · subst hai; simp [heq]
        · simp [hai, h1 a hai]
      cases hyi : y i <;> cases hzi : z i <;> simp_all
    · rw [if_neg h1]

lemma instr_cnot_unitary {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    circUnitary [.cnot i j hij] =
      permMat (fun q : Qubits n => Function.update q j (xor (q j) (q i))) := by
  ext y z
  simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one, instrApp]
  rw [embedOp_wire2]
  simp only [cnot, Matrix.of_apply, permMat]
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
        · subst haj; simp [h2.2]
        · by_cases hai : a = i
          · subst hai; simp [haj, h2.1]
          · simp [haj, h1 a hai haj]
      · cases hyi : y i <;> cases hyj : y j <;> cases hzi : z i <;> cases hzj : z j <;> simp_all
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

lemma act_cnot_ket {n : ℕ} (i j : Fin n) (hij : i ≠ j) (q : Qubits n) :
    act (circUnitary [.cnot i j hij]) (ket q) =
      ket (Function.update q j (xor (q j) (q i))) := by
  rw [instr_cnot_unitary, act_permMat]

lemma act_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (q : ι) :
    act (Matrix.diagonal d) (ket q) = d q • ket q := by
  apply WithLp.ofLp_injective
  funext y
  simp [act_ket, ket_apply, Matrix.diagonal_apply]
  by_cases h : y = q <;> simp [h]

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
  funext i; fin_cases i <;> rfl

lemma update_q3_1 (a b c b' : Bool) : Function.update (q3 a b c) 1 b' = q3 a b' c := by
  funext i; fin_cases i <;> rfl

lemma update_q3_2 (a b c c' : Bool) : Function.update (q3 a b c) 2 c' = q3 a b c' := by
  funext i; fin_cases i <;> rfl

def ket3 (a b : Bool) (α β : ℂ) : EuclideanSpace ℂ (Qubits 3) :=
  α • ket (q3 a b false) + β • ket (q3 a b true)

lemma ket3_h2 (a b : Bool) (α β : ℂ) :
    act (circUnitary [.h 2]) (ket3 a b α β) =
      ket3 a b (((Real.sqrt 2)⁻¹ : ℂ) * (α + β)) (((Real.sqrt 2)⁻¹ : ℂ) * (α - β)) := by
  simp only [ket3, act_add, act_smul, act_h_ket, q3_2, update_q3_2, Bool.false_eq_true, ↓reduceIte,
    one_smul]
  ext y
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

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
  by_cases h1 : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos h1]
    let extend : Qubits k → Qubits n :=
      fun v a => if ha : ∃ x : Fin k, w x = a then v (Classical.choose ha) else z a
    have hex_comp : ∀ v : Qubits k, extend v ∘ w = v := fun v => by
      ext x
      have hx : ∃ x' : Fin k, w x' = w x := ⟨x, rfl⟩
      dsimp only [Function.comp_def, extend]
      rw [dif_pos hx]
      congr 1
      exact w.injective (Classical.choose_spec hx)
    have hex_out : ∀ v : Qubits k, ∀ a : Fin n, a ∉ Set.range w → extend v a = z a := by
      intro v a ha
      have hnot : ¬ ∃ x : Fin k, w x = a := fun ⟨x, hx⟩ => ha ⟨x, hx⟩
      simp [extend, hnot]
    have hex_inj : Function.Injective extend := by
      intro v₁ v₂ hv
      have h := congrArg (fun f => f ∘ w) hv
      rwa [hex_comp, hex_comp] at h
    let S : Finset (Qubits n) :=
      Finset.univ.filter (fun q => ∀ a : Fin n, a ∉ Set.range w → q a = z a)
    have hsum_range : ∀ q ∈ S, q ∈ Set.range extend := by
      intro q hq
      have hqz : ∀ a : Fin n, a ∉ Set.range w → q a = z a := (Finset.mem_filter.mp hq).2
      refine ⟨q ∘ w, ?_⟩
      funext a
      dsimp only [extend]
      by_cases ha : ∃ x : Fin k, w x = a
      · rw [dif_pos ha, Function.comp_apply, Classical.choose_spec ha]
      · rw [dif_neg ha]; exact (hqz a fun ⟨x, hx⟩ => ha ⟨x, hx⟩).symm
    symm
    calc ∑ q : Qubits n,
            (if ∀ a : Fin n, a ∉ Set.range w → y a = q a then A (y ∘ w) (q ∘ w) else 0) *
              (if ∀ a : Fin n, a ∉ Set.range w → q a = z a then B (q ∘ w) (z ∘ w) else 0)
        = ∑ q ∈ S,
            (if ∀ a : Fin n, a ∉ Set.range w → y a = q a then A (y ∘ w) (q ∘ w) else 0) *
              (if ∀ a : Fin n, a ∉ Set.range w → q a = z a then B (q ∘ w) (z ∘ w) else 0) := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro q _ hq
          have hnq : ¬ ∀ a : Fin n, a ∉ Set.range w → q a = z a := fun h =>
            hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          rw [if_neg hnq, mul_zero]
      _ = ∑ v : Qubits k, A (y ∘ w) v * B v (z ∘ w) := by
          symm
          apply Finset.sum_bij (fun (v : Qubits k) _ => extend v)
          · intro v _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hex_out v⟩
          · intro v₁ _ v₂ _ h; exact hex_inj h
          · intro q hq
            obtain ⟨v, hv⟩ := hsum_range q hq
            exact ⟨v, Finset.mem_univ v, hv⟩
          · intro v _
            have hyq : ∀ a : Fin n, a ∉ Set.range w → y a = extend v a := fun a ha => by
              rw [hex_out v a ha]; exact h1 a ha
            rw [if_pos hyq, if_pos (hex_out v), hex_comp]
  · rw [if_neg h1]
    symm
    apply Finset.sum_eq_zero
    intro q _
    by_cases hq1 : ∀ a : Fin n, a ∉ Set.range w → y a = q a
    · rw [if_pos hq1]
      have hq2 : ¬ ∀ a : Fin n, a ∉ Set.range w → q a = z a := by
        intro hq2
        apply h1
        intro a ha
        exact (hq1 a ha).trans (hq2 a ha)
      rw [if_neg hq2, mul_zero]
    · rw [if_neg hq1, zero_mul]

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

lemma circUnitary_cons {n : ℕ} (g : Instr n) (c : List (Instr n)) :
    circUnitary (g :: c) = circUnitary c * circUnitary [g] := by
  have h : g :: c = [g] ++ c := rfl
  rw [h, circUnitary_append]

lemma embedOp_one {k n : ℕ} (w : Fin k ↪ Fin n) :
    embedOp (1 : Matrix (Qubits k) (Qubits k) ℂ) w = 1 := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz
    rw [if_pos (fun _ _ => rfl), if_pos rfl, if_pos rfl]
  · rw [if_neg hyz]
    by_cases hout : ∀ a : Fin n, a ∉ Set.range w → y a = z a
    · rw [if_pos hout]
      have hcomp : y ∘ w ≠ z ∘ w := by
        intro hcomp
        apply hyz
        funext a
        by_cases ha : ∃ x : Fin k, w x = a
        · obtain ⟨x, rfl⟩ := ha
          exact congrFun hcomp x
        · exact hout a (fun ⟨x, hx⟩ => ha ⟨x, hx⟩)
      rw [if_neg hcomp]
    · rw [if_neg hout]

lemma embedOp_trans {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w₁ : Fin k ↪ Fin m) (w₂ : Fin m ↪ Fin n) :
    embedOp (embedOp M w₁) w₂ = embedOp M (w₁.trans w₂) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range (w₁.trans w₂) → y a = z a) ↔
      (∀ a : Fin n, a ∉ Set.range w₂ → y a = z a) ∧
        (∀ b : Fin m, b ∉ Set.range w₁ → y (w₂ b) = z (w₂ b)) := by
    constructor
    · intro h
      refine ⟨fun a ha => h a ?_, fun b hb => h (w₂ b) ?_⟩
      · rintro ⟨x, hx⟩
        apply ha
        exact ⟨w₁ x, hx⟩
      · rintro ⟨x, hx⟩
        apply hb
        exact ⟨x, w₂.injective hx⟩
    · rintro ⟨h2, h1⟩ a ha
      by_cases ha2 : ∃ b : Fin m, w₂ b = a
      · obtain ⟨b, rfl⟩ := ha2
        apply h1 b
        rintro ⟨x, rfl⟩
        exact ha ⟨x, rfl⟩
      · exact h2 a (fun ⟨b, hb⟩ => ha2 ⟨b, hb⟩)
  by_cases h12 : ∀ a : Fin n, a ∉ Set.range (w₁.trans w₂) → y a = z a
  · obtain ⟨h2, h1⟩ := hiff.mp h12
    rw [if_pos h12, if_pos h2]
    have h1' : ∀ b : Fin m, b ∉ Set.range w₁ → (y ∘ w₂) b = (z ∘ w₂) b := h1
    rw [if_pos h1']
    rfl
  · rw [if_neg h12]
    by_cases h2 : ∀ a : Fin n, a ∉ Set.range w₂ → y a = z a
    · rw [if_pos h2]
      have hn1 : ¬ ∀ b : Fin m, b ∉ Set.range w₁ → (y ∘ w₂) b = (z ∘ w₂) b := fun h1 =>
        h12 (hiff.mpr ⟨h2, h1⟩)
      rw [if_neg hn1]
    · rw [if_neg h2]

def mapInstr {k n : ℕ} (w : Fin k ↪ Fin n) : Instr k → Instr n
  | .h i => .h (w i)
  | .s i => .s (w i)
  | .t i => .t (w i)
  | .x i => .x (w i)
  | .cnot i j hij => .cnot (w i) (w j) (w.injective.ne hij)

def mapCirc {k n : ℕ} (w : Fin k ↪ Fin n) (c : List (Instr k)) : List (Instr n) :=
  c.map (mapInstr w)

lemma wire1_trans {k n : ℕ} (w : Fin k ↪ Fin n) (i : Fin k) :
    wire1 (w i) = (wire1 i).trans w := by
  ext x
  rfl

lemma wire2_trans {k n : ℕ} (w : Fin k ↪ Fin n) (i j : Fin k) (hij : i ≠ j) :
    wire2 (w i) (w j) (w.injective.ne hij) = (wire2 i j hij).trans w := by
  ext x
  fin_cases x <;> rfl

lemma circUnitary_singleton_mapInstr {k n : ℕ} (w : Fin k ↪ Fin n) (g : Instr k) :
    circUnitary [mapInstr w g] = embedOp (circUnitary [g]) w := by
  cases g with
  | h i =>
    simp only [mapInstr, circUnitary, Circuit.unitary, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil,
      mul_one, instrApp]
    rw [show (wire1 (w i) : Fin (Gate.ofMatrix1 hadamard).arity ↪ Fin n) = (wire1 i).trans w from wire1_trans w i]
    exact (embedOp_trans (Gate.ofMatrix1 hadamard).mat (wire1 i) w).symm
  | s i =>
    simp only [mapInstr, circUnitary, Circuit.unitary, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil,
      mul_one, instrApp]
    rw [show (wire1 (w i) : Fin (Gate.ofMatrix1 phaseS).arity ↪ Fin n) = (wire1 i).trans w from wire1_trans w i]
    exact (embedOp_trans (Gate.ofMatrix1 phaseS).mat (wire1 i) w).symm
  | t i =>
    simp only [mapInstr, circUnitary, Circuit.unitary, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil,
      mul_one, instrApp]
    rw [show (wire1 (w i) : Fin (Gate.ofMatrix1 gateT).arity ↪ Fin n) = (wire1 i).trans w from wire1_trans w i]
    exact (embedOp_trans (Gate.ofMatrix1 gateT).mat (wire1 i) w).symm
  | x i =>
    simp only [mapInstr, circUnitary, Circuit.unitary, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil,
      mul_one, instrApp]
    rw [show (wire1 (w i) : Fin (Gate.ofMatrix1 pauliX).arity ↪ Fin n) = (wire1 i).trans w from wire1_trans w i]
    exact (embedOp_trans (Gate.ofMatrix1 pauliX).mat (wire1 i) w).symm
  | cnot i j hij =>
    simp only [mapInstr, circUnitary, Circuit.unitary, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil,
      mul_one, instrApp]
    rw [show (wire2 (w i) (w j) (w.injective.ne hij) : Fin (Gate.ofMatrix2 cnot).arity ↪ Fin n) =
      (wire2 i j hij).trans w from wire2_trans w i j hij]
    exact (embedOp_trans (Gate.ofMatrix2 cnot).mat (wire2 i j hij) w).symm

lemma circUnitary_mapCirc {k n : ℕ} (w : Fin k ↪ Fin n) (c : List (Instr k)) :
    circUnitary (mapCirc w c) = embedOp (circUnitary c) w := by
  induction c with
  | nil =>
    simp [mapCirc, circUnitary_nil, embedOp_one]
  | cons g cs ih =>
    have hcons1 : circUnitary (mapCirc w (g :: cs)) =
        circUnitary (mapCirc w cs) * circUnitary [mapInstr w g] := circUnitary_cons _ _
    have hcons2 : circUnitary (g :: cs) = circUnitary cs * circUnitary [g] := circUnitary_cons _ _
    rw [hcons1, hcons2, ih, circUnitary_singleton_mapInstr w g, embedOp_mul]

def wire3 {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Fin 3 ↪ Fin n where
  toFun := ![a, b, c]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] lemma wire3_0 {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    wire3 a b c hab hac hbc 0 = a := rfl
@[simp] lemma wire3_1 {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    wire3 a b c hab hac hbc 1 = b := rfl
@[simp] lemma wire3_2 {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    wire3 a b c hab hac hbc 2 = c := rfl

lemma embedOp_wire3_ccx {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    embedOp (permMat (fun q : Qubits 3 => Function.update q 2 (xor (q 2) (q 0 && q 1))))
        (wire3 a b c hab hac hbc) =
      permMat (fun q : Qubits n => Function.update q c (xor (q c) (q a && q b))) := by
  ext y z
  simp only [embedOp, permMat, Matrix.of_apply]
  have hiff_out : (∀ t : Fin n, t ∉ Set.range (wire3 a b c hab hac hbc) → y t = z t) ↔
      ∀ t : Fin n, t ≠ a → t ≠ b → t ≠ c → y t = z t := by
    constructor
    · intro h t hta htb htc
      apply h t
      rintro ⟨i, rfl⟩
      fin_cases i <;> contradiction
    · intro h t ht
      exact h t (fun hta => ht ⟨0, hta.symm⟩) (fun htb => ht ⟨1, htb.symm⟩)
        (fun htc => ht ⟨2, htc.symm⟩)
  by_cases hy : y = Function.update z c (xor (z c) (z a && z b))
  · subst hy
    have hout : ∀ t : Fin n, t ∉ Set.range (wire3 a b c hab hac hbc) →
        Function.update z c (xor (z c) (z a && z b)) t = z t :=
      hiff_out.mpr (fun t _ _ htc => by simp [htc])
    rw [if_pos hout, if_pos rfl]
    have hcomp : (Function.update z c (xor (z c) (z a && z b))) ∘ wire3 a b c hab hac hbc =
        Function.update (z ∘ wire3 a b c hab hac hbc) 2
          (xor ((z ∘ wire3 a b c hab hac hbc) 2)
            ((z ∘ wire3 a b c hab hac hbc) 0 && (z ∘ wire3 a b c hab hac hbc) 1)) := by
      funext i
      fin_cases i
      · simp [hac]
      · simp [hbc]
      · simp
    rw [if_pos hcomp]
  · rw [if_neg hy]
    by_cases hout : ∀ t : Fin n, t ∉ Set.range (wire3 a b c hab hac hbc) → y t = z t
    · rw [if_pos hout]
      have hout' := hiff_out.mp hout
      have hne : y ∘ wire3 a b c hab hac hbc ≠
          Function.update (z ∘ wire3 a b c hab hac hbc) 2
            (xor ((z ∘ wire3 a b c hab hac hbc) 2)
              ((z ∘ wire3 a b c hab hac hbc) 0 && (z ∘ wire3 a b c hab hac hbc) 1)) := by
        intro hcomp
        apply hy
        funext t
        by_cases htc : t = c
        · subst htc
          simpa using congrFun hcomp 2
        · by_cases hta : t = a
          · subst hta
            have := congrFun hcomp 0
            simpa [hac] using this
          · by_cases htb : t = b
            · subst htb
              have := congrFun hcomp 1
              simpa [hbc] using this
            · simp [htc, hout' t hta htb htc]
      rw [if_neg hne]
    · rw [if_neg hout]

inductive RevGate (n : ℕ) : Type
  | x (i : Fin n)
  | cnot (c t : Fin n) (h : c ≠ t)
  | ccx (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)

def evalRev {n : ℕ} : RevGate n → Qubits n → Qubits n
  | .x i, q => Function.update q i (!q i)
  | .cnot c t _, q => Function.update q t (xor (q t) (q c))
  | .ccx a b t _ _ _, q => Function.update q t (xor (q t) (q a && q b))

@[simp] lemma evalRev_x {n : ℕ} (i : Fin n) (q : Qubits n) :
    evalRev (.x i) q = Function.update q i (!q i) := rfl

@[simp] lemma evalRev_cnot {n : ℕ} (c t : Fin n) (h : c ≠ t) (q : Qubits n) :
    evalRev (.cnot c t h) q = Function.update q t (xor (q t) (q c)) := rfl

@[simp] lemma evalRev_ccx {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (q : Qubits n) :
    evalRev (.ccx a b t hab hat hbt) q = Function.update q t (xor (q t) (q a && q b)) := rfl

lemma evalRev_involutive {n : ℕ} (g : RevGate n) (q : Qubits n) :
    evalRev g (evalRev g q) = q := by
  cases g with
  | x i =>
    funext k
    by_cases hk : k = i
    · subst hk; cases h : q k <;> simp [h]
    · simp [hk]
  | cnot c t h =>
    funext k
    by_cases hkt : k = t
    · subst hkt
      have hc : c ≠ k := h
      cases hqk : q k <;> cases hqc : q c <;> simp [hqk, hqc, hc]
    · simp [hkt]
  | ccx a b t hab hat hbt =>
    funext k
    by_cases hkt : k = t
    · subst hkt
      cases hqk : q k <;> cases hqa : q a <;> cases hqb : q b <;> simp [hqk, hqa, hqb, hat, hbt]
    · simp [hkt]

def evalRevList {n : ℕ} (c : List (RevGate n)) (q : Qubits n) : Qubits n :=
  c.foldl (fun acc g => evalRev g acc) q

@[simp] lemma evalRevList_nil {n : ℕ} (q : Qubits n) : evalRevList [] q = q := rfl

@[simp] lemma evalRevList_cons {n : ℕ} (g : RevGate n) (c : List (RevGate n)) (q : Qubits n) :
    evalRevList (g :: c) q = evalRevList c (evalRev g q) := rfl

lemma evalRevList_append {n : ℕ} (c₁ c₂ : List (RevGate n)) (q : Qubits n) :
    evalRevList (c₁ ++ c₂) q = evalRevList c₂ (evalRevList c₁ q) :=
  List.foldl_append

lemma evalRevList_reverse {n : ℕ} (c : List (RevGate n)) (q : Qubits n) :
    evalRevList c.reverse (evalRevList c q) = q := by
  induction c generalizing q with
  | nil => rfl
  | cons g gs ih =>
    rw [List.reverse_cons, evalRevList_cons, evalRevList_append, ih]
    simp only [evalRevList, List.foldl_cons, List.foldl_nil]
    exact evalRev_involutive g q

lemma evalRevList_reverse_cancel {n : ℕ} (c : List (RevGate n)) (q : Qubits n) :
    evalRevList c (evalRevList c.reverse q) = q := by
  simpa using evalRevList_reverse c.reverse q

def compileRevGate {n : ℕ} : RevGate n → List (Instr n)
  | .x i => [.x i]
  | .cnot c t h => [.cnot c t h]
  | .ccx a b t hab hat hbt => mapCirc (wire3 a b t hab hat hbt) ccx3

def compileRev {n : ℕ} (c : List (RevGate n)) : List (Instr n) :=
  c.flatMap compileRevGate

lemma ccx3_length : ccx3.length = 24 := by decide

lemma compileRevGate_length_le {n : ℕ} (g : RevGate n) :
    (compileRevGate g).length ≤ 24 := by
  cases g with
  | x i => simp [compileRevGate]
  | cnot c t h => simp [compileRevGate]
  | ccx a b t hab hat hbt =>
    simp [compileRevGate, mapCirc, List.length_map, ccx3_length]

lemma compileRev_length_le {n : ℕ} (c : List (RevGate n)) :
    (compileRev c).length ≤ 24 * c.length := by
  induction c with
  | nil => simp [compileRev]
  | cons g gs ih =>
    simp only [compileRev, List.flatMap_cons, List.length_append, List.length_cons]
    have hg := compileRevGate_length_le g
    have hgs : (gs.flatMap compileRevGate).length ≤ 24 * gs.length := ih
    omega

lemma circUnitary_compileRevGate {n : ℕ} (g : RevGate n) :
    circUnitary (compileRevGate g) = permMat (evalRev g) := by
  cases g with
  | x i => exact instr_x_unitary i
  | cnot c t h => exact instr_cnot_unitary c t h
  | ccx a b t hab hat hbt =>
    simp only [compileRevGate]
    rw [circUnitary_mapCirc, circUnitary_ccx3, embedOp_wire3_ccx]
    rfl

lemma circUnitary_compileRev {n : ℕ} (c : List (RevGate n)) :
    circUnitary (compileRev c) = permMat (evalRevList c) := by
  induction c with
  | nil =>
    have h : evalRevList ([] : List (RevGate n)) = id := rfl
    rw [h, permMat_id]
    simp [compileRev, circUnitary_nil]
  | cons g gs ih =>
    have h1 : compileRev (g :: gs) = compileRevGate g ++ compileRev gs := rfl
    rw [h1, circUnitary_append, ih, circUnitary_compileRevGate, permMat_mul]
    congr 1

def swapRev {n : ℕ} (a b : Fin n) (hab : a ≠ b) : List (RevGate n) :=
  [.cnot a b hab, .cnot b a hab.symm, .cnot a b hab]

lemma evalRevList_swapRev {n : ℕ} (a b : Fin n) (hab : a ≠ b) (q : Qubits n) :
    evalRevList (swapRev a b hab) q = Function.update (Function.update q a (q b)) b (q a) := by
  simp only [swapRev, evalRevList_cons, evalRevList_nil, evalRev_cnot]
  funext i
  by_cases hia : i = a
  · subst hia
    have hab' : i ≠ b := hab
    cases hi : q i <;> cases hb : q b <;> simp [hi, hab', hab.symm]
  · by_cases hib : i = b
    · subst hib
      cases ha : q a <;> cases hi : q i <;> simp [ha, hia, hab]
    · simp [hia, hib]

lemma act_sum {ι α : Type} [Fintype ι] (M : Matrix ι ι ℂ) (s : Finset α)
    (f : α → EuclideanSpace ℂ ι) :
    act M (∑ a ∈ s, f a) = ∑ a ∈ s, act M (f a) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    apply WithLp.ofLp_injective
    funext y
    simp [act, Matrix.mulVec_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, act_add, ih]

lemma embedVec_eq_sum_ket {X : Type} [Fintype X] {n : ℕ}
    (code : X → Qubits n) (ψ : EuclideanSpace ℂ X) :
    embedVec code ψ = ∑ x : X, ψ.ofLp x • ket (code x) := by
  apply WithLp.ofLp_injective
  funext y
  simp only [embedVec, WithLp.ofLp_toLp]
  have hsum : (WithLp.ofLp (∑ x : X, ψ.ofLp x • ket (code x))) y =
      ∑ x : X, ψ.ofLp x * (if y = code x then 1 else 0) := by
    induction (Finset.univ : Finset X) using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      simp [ket_apply, ih]
  rw [hsum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : code x = y
  · subst h; simp
  · simp [h, Ne.symm h]

lemma implements_of_permMat {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y] {n : ℕ}
    (f : Qubits n → Qubits n) (cin : X → Qubits n) (cout : Y → Qubits n) (g : X → Y)
    (hmap : ∀ x : X, f (cin x) = cout (g x)) (ε : ℝ) (hε : 0 ≤ ε) :
    Implements (permMat f) cin cout (permMat g) ε := by
  intro ψ
  have heq : act (permMat f) (embedVec cin ψ) =
      embedVec cout (WithLp.toLp 2 ((permMat g).mulVec ψ.ofLp)) := by
    rw [embedVec_eq_sum_ket, act_sum]
    have hL : (∑ x : X, act (permMat f) (ψ.ofLp x • ket (cin x))) =
        ∑ x : X, ψ.ofLp x • ket (cout (g x)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [act_smul, act_permMat, hmap x]
    rw [hL, embedVec_eq_sum_ket]
    have hR1 : (∑ y : Y, (∑ x : X, (if y = g x then 1 else 0) * ψ.ofLp x) • ket (cout y)) =
        ∑ y : Y, ∑ x : X, (if y = g x then ψ.ofLp x else 0) • ket (cout y) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    simp only [Matrix.mulVec, dotProduct, permMat, Matrix.of_apply] at hR1 ⊢
    rw [hR1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single (g x)]
    · simp
    · intro y _ hy; simp [hy]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [heq, sub_self, norm_zero]
  exact mul_nonneg hε (norm_nonneg ψ)

/-! ### Section 3: Reversible modular arithmetic and `fbOutCirc` -/

def regVal {n : ℕ} (q : Qubits n) (X : ℕ → Fin n) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, (q (X j)).toNat * 2 ^ j

@[simp] lemma regVal_zero {n : ℕ} (q : Qubits n) (X : ℕ → Fin n) :
    regVal q X 0 = 0 := rfl

lemma regVal_succ {n : ℕ} (q : Qubits n) (X : ℕ → Fin n) (k : ℕ) :
    regVal q X (k + 1) = regVal q X k + (q (X k)).toNat * 2 ^ k := by
  simp [regVal, Finset.sum_range_succ]

lemma regVal_lt {n : ℕ} (q : Qubits n) (X : ℕ → Fin n) (k : ℕ) :
    regVal q X k < 2 ^ k := by
  induction k with
  | zero => simp [regVal]
  | succ k ih =>
    rw [regVal_succ, pow_succ]
    have hb : (q (X k)).toNat ≤ 1 := by cases q (X k) <;> simp
    nlinarith

lemma regVal_eq_of_eq {n : ℕ} {q₁ q₂ : Qubits n} {X : ℕ → Fin n} {k : ℕ}
    (h : ∀ j < k, q₁ (X j) = q₂ (X j)) : regVal q₁ X k = regVal q₂ X k := by
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h j (Finset.mem_range.mp hj)]

lemma regVal_update_of_not_mem {n : ℕ} (q : Qubits n) (X : ℕ → Fin n) (k : ℕ)
    (w : Fin n) (b : Bool) (hw : ∀ j < k, X j ≠ w) :
    regVal (Function.update q w b) X k = regVal q X k := by
  apply regVal_eq_of_eq
  intro j hj
  simp [hw j hj]

lemma regVal_eq_zero_of_all_false {n : ℕ} {q : Qubits n} {X : ℕ → Fin n} {k : ℕ}
    (h : ∀ j < k, q (X j) = false) : regVal q X k = 0 := by
  simp only [regVal]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [h j (Finset.mem_range.mp hj)]
  simp

lemma sum_bool_lt (f : ℕ → Bool) (k : ℕ) :
    ∑ j ∈ Finset.range k, (f j).toNat * 2 ^ j < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    cases f k <;> simp <;> omega

lemma sum_bits_testBit (f : ℕ → Bool) (k i : ℕ) :
    (∑ j ∈ Finset.range k, (f j).toNat * 2 ^ j).testBit i =
      if i < k then f i else false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    set S := ∑ j ∈ Finset.range k, (f j).toNat * 2 ^ j
    have hS : S < 2 ^ k := sum_bool_lt f k
    have hS' : S + (f k).toNat * 2 ^ k < 2 ^ (k + 1) := by
      rw [pow_succ]
      cases f k <;> simp <;> omega
    by_cases hik : i < k
    · rw [if_pos (by omega), Nat.testBit_eq_decide_div_mod_eq]
      have hk : k = i + 1 + (k - i - 1) := by omega
      have hpow : 2 ^ k = 2 ^ i * (2 * 2 ^ (k - i - 1)) := by
        calc 2 ^ k = 2 ^ (i + 1 + (k - i - 1)) := by rw [← hk]
          _ = 2 ^ (i + 1) * 2 ^ (k - i - 1) := pow_add 2 (i + 1) (k - i - 1)
          _ = (2 ^ i * 2) * 2 ^ (k - i - 1) := by rw [pow_succ]
          _ = 2 ^ i * (2 * 2 ^ (k - i - 1)) := by ring
      have hdiv : (S + (f k).toNat * 2 ^ k) / 2 ^ i =
          S / 2 ^ i + 2 * ((f k).toNat * 2 ^ (k - i - 1)) := by
        rw [hpow, show (f k).toNat * (2 ^ i * (2 * 2 ^ (k - i - 1))) =
            (2 * ((f k).toNat * 2 ^ (k - i - 1))) * 2 ^ i by ring,
          Nat.add_mul_div_right _ _ (by positivity)]
      rw [hdiv, Nat.add_mul_mod_self_left]
      have ih' := ih
      rw [if_pos hik, Nat.testBit_eq_decide_div_mod_eq] at ih'
      exact ih'
    · by_cases hieq : i = k
      · subst hieq
        rw [if_pos (Nat.lt_succ_self i), Nat.testBit_eq_decide_div_mod_eq]
        rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hS, zero_add]
        cases f i <;> simp
      · have hgt : k + 1 ≤ i := by omega
        rw [if_neg (by omega)]
        apply Nat.testBit_lt_two_pow
        have hpow : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hgt
        omega

lemma regVal_testBit {n : ℕ} (q : Qubits n) (X : ℕ → Fin n) {k j : ℕ} (hj : j < k) :
    (regVal q X k).testBit j = q (X j) := by
  unfold regVal
  rw [sum_bits_testBit (fun t => q (X t)) k j, if_pos hj]

lemma regVal_eq_of_testBit {n : ℕ} {q : Qubits n} {X : ℕ → Fin n} {k m : ℕ}
    (hm : m < 2 ^ k) (h : ∀ j < k, q (X j) = m.testBit j) :
    regVal q X k = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · rw [regVal_testBit q X hi, h i hi]
  · have h1 : regVal q X k < 2 ^ i := lt_of_lt_of_le (regVal_lt q X k)
      (Nat.pow_le_pow_right (by decide) (by omega))
    have h2 : m < 2 ^ i := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

structure AddWires (n k : ℕ) where
  A : ℕ → Fin n
  B : ℕ → Fin n
  S : ℕ → Fin n
  C : ℕ → Fin n
  S_inj : ∀ i < k, ∀ j < k, S i = S j → i = j
  C_inj : ∀ i ≤ k, ∀ j ≤ k, C i = C j → i = j
  AB : ∀ i < k, ∀ j < k, A i ≠ B j
  AS : ∀ i < k, ∀ j < k, A i ≠ S j
  AC : ∀ i < k, ∀ j ≤ k, A i ≠ C j
  BS : ∀ i < k, ∀ j < k, B i ≠ S j
  BC : ∀ i < k, ∀ j ≤ k, B i ≠ C j
  SC : ∀ i < k, ∀ j ≤ k, S i ≠ C j

def rippleAddStep {n k : ℕ} (w : AddWires n k) (j : ℕ) (hj : j < k) : List (RevGate n) :=
  [ .cnot (w.A j) (w.S j) (w.AS j hj j hj),
    .cnot (w.B j) (w.S j) (w.BS j hj j hj),
    .ccx (w.A j) (w.B j) (w.C (j + 1)) (w.AB j hj j hj) (w.AC j hj (j + 1) hj) (w.BC j hj (j + 1) hj),
    .ccx (w.C j) (w.S j) (w.C (j + 1)) (w.SC j hj j (Nat.le_of_lt hj)).symm
      (w.C_inj j (Nat.le_of_lt hj) (j + 1) hj |>.mt (by omega))
      (w.SC j hj (j + 1) hj),
    .cnot (w.C j) (w.S j) (w.SC j hj j (Nat.le_of_lt hj)).symm ]

def rippleAddGo {n k : ℕ} (w : AddWires n k) : ∀ m ≤ k, List (RevGate n)
  | 0, _ => []
  | m + 1, hm => rippleAddGo w m (Nat.le_of_lt hm) ++ rippleAddStep w m hm

def rippleAdd {n k : ℕ} (w : AddWires n k) : List (RevGate n) :=
  rippleAddGo w k le_rfl

lemma rippleAddStep_length {n k : ℕ} (w : AddWires n k) (j : ℕ) (hj : j < k) :
    (rippleAddStep w j hj).length = 5 := rfl

lemma rippleAddGo_length {n k : ℕ} (w : AddWires n k) :
    ∀ m (hm : m ≤ k), (rippleAddGo w m hm).length = 5 * m
  | 0, _ => rfl
  | m + 1, hm => by
    simp [rippleAddGo, rippleAddGo_length w m (Nat.le_of_lt hm), rippleAddStep_length, Nat.mul_succ]

lemma rippleAdd_length {n k : ℕ} (w : AddWires n k) :
    (rippleAdd w).length = 5 * k :=
  rippleAddGo_length w k le_rfl

lemma rippleAddStep_spec {n k : ℕ} (w : AddWires n k) (j : ℕ) (hj : j < k) (q : Qubits n)
    (hSj : q (w.S j) = false) (hCj : q (w.C (j + 1)) = false) :
    let q' := evalRevList (rippleAddStep w j hj) q
    (∀ z : Fin n, z ≠ w.S j → z ≠ w.C (j + 1) → q' z = q z) ∧
      (q' (w.S j)).toNat + 2 * (q' (w.C (j + 1))).toNat =
        (q (w.A j)).toNat + (q (w.B j)).toNat + (q (w.C j)).toNat := by
  intro q'
  have h1 : w.A j ≠ w.B j := w.AB j hj j hj
  have h2 : w.A j ≠ w.S j := w.AS j hj j hj
  have h3 : w.A j ≠ w.C j := w.AC j hj j (Nat.le_of_lt hj)
  have h4 : w.A j ≠ w.C (j + 1) := w.AC j hj (j + 1) hj
  have h5 : w.B j ≠ w.S j := w.BS j hj j hj
  have h6 : w.B j ≠ w.C j := w.BC j hj j (Nat.le_of_lt hj)
  have h7 : w.B j ≠ w.C (j + 1) := w.BC j hj (j + 1) hj
  have h8 : w.S j ≠ w.C j := w.SC j hj j (Nat.le_of_lt hj)
  have h9 : w.S j ≠ w.C (j + 1) := w.SC j hj (j + 1) hj
  have h10 : w.C j ≠ w.C (j + 1) := fun h => by
    have := w.C_inj j (Nat.le_of_lt hj) (j + 1) hj h; omega
  have hS : q' (w.S j) = xor (xor (q (w.A j)) (q (w.B j))) (q (w.C j)) := by
    simp only [q', rippleAddStep, evalRevList_cons, evalRevList_nil, evalRev_cnot, evalRev_ccx]
    cases ha : q (w.A j) <;> cases hb : q (w.B j) <;> cases hc : q (w.C j) <;>
      simp [hSj, hCj, ha, hb, hc, h2, h5, h8.symm, h9, h10, h9.symm]
  have hC : q' (w.C (j + 1)) =
      xor (q (w.A j) && q (w.B j)) (q (w.C j) && xor (q (w.A j)) (q (w.B j))) := by
    simp only [q', rippleAddStep, evalRevList_cons, evalRevList_nil, evalRev_cnot, evalRev_ccx]
    cases ha : q (w.A j) <;> cases hb : q (w.B j) <;> cases hc : q (w.C j) <;>
      simp [hSj, hCj, ha, hb, hc, h2, h5, h8.symm, h9, h10, h9.symm]
  refine ⟨?_, ?_⟩
  · intro z hzS hzC
    simp only [q', rippleAddStep, evalRevList_cons, evalRevList_nil, evalRev_cnot, evalRev_ccx]
    simp [hzS, hzC]
  · rw [hS, hC]
    cases q (w.A j) <;> cases q (w.B j) <;> cases q (w.C j) <;> decide

lemma rippleAddGo_spec {n k : ℕ} (w : AddWires n k) :
    ∀ m (hm : m ≤ k) (q : Qubits n),
      (∀ t < m, q (w.S t) = false) → (∀ t, 1 ≤ t → t ≤ m → q (w.C t) = false) →
      let q' := evalRevList (rippleAddGo w m hm) q
      (∀ z : Fin n, (∀ t < m, z ≠ w.S t) → (∀ t, 1 ≤ t → t ≤ m → z ≠ w.C t) → q' z = q z) ∧
        regVal q' w.S m + (q' (w.C m)).toNat * 2 ^ m =
          regVal q w.A m + regVal q w.B m + (q (w.C 0)).toNat
  | 0, _, q, _, _ => by
    refine ⟨fun z _ _ => rfl, ?_⟩
    simp [rippleAddGo, regVal]
  | m + 1, hm, q, hS, hC => by
    have hm' : m ≤ k := Nat.le_of_lt hm
    have ih := rippleAddGo_spec w m hm' q (fun t ht => hS t (by omega)) (fun t ht1 ht2 => hC t ht1 (by omega))
    set q₁ := evalRevList (rippleAddGo w m hm') q
    have hq₁_frame : ∀ z : Fin n, (∀ t < m, z ≠ w.S t) → (∀ t, 1 ≤ t → t ≤ m → z ≠ w.C t) →
        q₁ z = q z := ih.1
    have hq₁_arith : regVal q₁ w.S m + (q₁ (w.C m)).toNat * 2 ^ m =
        regVal q w.A m + regVal q w.B m + (q (w.C 0)).toNat := ih.2
    have hSm : q₁ (w.S m) = false := by
      rw [hq₁_frame (w.S m) (fun t ht heq => by have := w.S_inj m hm t (by omega) heq; omega)
        (fun t _ ht heq => w.SC m hm t (by omega) heq)]
      exact hS m (Nat.lt_succ_self m)
    have hCm1 : q₁ (w.C (m + 1)) = false := by
      rw [hq₁_frame (w.C (m + 1)) (fun t ht heq => (w.SC t (by omega) (m + 1) hm heq.symm))
        (fun t _ ht heq => by have := w.C_inj (m + 1) hm t (by omega) heq; omega)]
      exact hC (m + 1) (by omega) (le_refl _)
    have hstep := rippleAddStep_spec w m hm q₁ hSm hCm1
    set q₂ := evalRevList (rippleAddStep w m hm) q₁
    have hq₂_eq : evalRevList (rippleAddGo w (m + 1) hm) q = q₂ := by
      simp [rippleAddGo, evalRevList_append, q₁, q₂]
    rw [hq₂_eq]
    refine ⟨?_, ?_⟩
    · intro z hzS hzC
      have hzSm : z ≠ w.S m := hzS m (Nat.lt_succ_self m)
      have hzCm1 : z ≠ w.C (m + 1) := hzC (m + 1) (by omega) (le_refl _)
      rw [hstep.1 z hzSm hzCm1]
      exact hq₁_frame z (fun t ht => hzS t (by omega)) (fun t ht1 ht2 => hzC t ht1 (by omega))
    · have hS_eq : regVal q₂ w.S m = regVal q₁ w.S m := by
        apply regVal_eq_of_eq
        intro t ht
        exact hstep.1 (w.S t) (fun heq => by have := w.S_inj t (by omega) m hm heq; omega)
          (w.SC t (by omega) (m + 1) hm)
      have hAm_eq : q₁ (w.A m) = q (w.A m) :=
        hq₁_frame (w.A m) (fun t ht => w.AS m hm t (by omega)) (fun t _ ht => w.AC m hm t (by omega))
      have hBm_eq : q₁ (w.B m) = q (w.B m) :=
        hq₁_frame (w.B m) (fun t ht => w.BS m hm t (by omega)) (fun t _ ht => w.BC m hm t (by omega))
      rw [regVal_succ q₂ w.S m, hS_eq, regVal_succ q w.A m, regVal_succ q w.B m, pow_succ]
      have hs := hstep.2
      rw [hAm_eq, hBm_eq] at hs
      have hm_mul := congrArg (· * 2 ^ m) hs
      nlinarith

lemma rippleAdd_spec {n k : ℕ} (w : AddWires n k) (q : Qubits n)
    (hS : ∀ t < k, q (w.S t) = false) (hC : ∀ t ≤ k, q (w.C t) = false) :
    let q' := evalRevList (rippleAdd w) q
    (∀ z : Fin n, (∀ t < k, z ≠ w.S t) → (∀ t, 1 ≤ t → t ≤ k → z ≠ w.C t) → q' z = q z) ∧
      regVal q' w.S k + (q' (w.C k)).toNat * 2 ^ k = regVal q w.A k + regVal q w.B k := by
  have h := rippleAddGo_spec w k le_rfl q hS (fun t _ ht2 => hC t ht2)
  have hC0 : q (w.C 0) = false := hC 0 (Nat.zero_le k)
  simpa [rippleAdd, hC0] using h

structure SubWires (n k : ℕ) where
  X : ℕ → Fin n
  Y : ℕ → Fin n
  D : ℕ → Fin n
  Br : ℕ → Fin n
  D_inj : ∀ i < k, ∀ j < k, D i = D j → i = j
  Br_inj : ∀ i ≤ k, ∀ j ≤ k, Br i = Br j → i = j
  XY : ∀ i < k, ∀ j < k, X i ≠ Y j
  XD : ∀ i < k, ∀ j < k, X i ≠ D j
  XBr : ∀ i < k, ∀ j ≤ k, X i ≠ Br j
  YD : ∀ i < k, ∀ j < k, Y i ≠ D j
  YBr : ∀ i < k, ∀ j ≤ k, Y i ≠ Br j
  DBr : ∀ i < k, ∀ j ≤ k, D i ≠ Br j

def rippleSubStep {n k : ℕ} (w : SubWires n k) (j : ℕ) (hj : j < k) : List (RevGate n) :=
  [ .cnot (w.X j) (w.D j) (w.XD j hj j hj),
    .x (w.D j),
    .ccx (w.D j) (w.Y j) (w.Br (j + 1)) (w.YD j hj j hj).symm
      (w.DBr j hj (j + 1) hj) (w.YBr j hj (j + 1) hj),
    .cnot (w.Y j) (w.D j) (w.YD j hj j hj),
    .ccx (w.Br j) (w.D j) (w.Br (j + 1)) (w.DBr j hj j (Nat.le_of_lt hj)).symm
      (w.Br_inj j (Nat.le_of_lt hj) (j + 1) hj |>.mt (by omega))
      (w.DBr j hj (j + 1) hj),
    .x (w.D j),
    .cnot (w.Br j) (w.D j) (w.DBr j hj j (Nat.le_of_lt hj)).symm ]

def rippleSubGo {n k : ℕ} (w : SubWires n k) : ∀ m ≤ k, List (RevGate n)
  | 0, _ => []
  | m + 1, hm => rippleSubGo w m (Nat.le_of_lt hm) ++ rippleSubStep w m hm

def rippleSub {n k : ℕ} (w : SubWires n k) : List (RevGate n) :=
  rippleSubGo w k le_rfl

lemma rippleSubStep_length {n k : ℕ} (w : SubWires n k) (j : ℕ) (hj : j < k) :
    (rippleSubStep w j hj).length = 7 := rfl

lemma rippleSubGo_length {n k : ℕ} (w : SubWires n k) :
    ∀ m (hm : m ≤ k), (rippleSubGo w m hm).length = 7 * m
  | 0, _ => rfl
  | m + 1, hm => by
    simp [rippleSubGo, rippleSubGo_length w m (Nat.le_of_lt hm), rippleSubStep_length, Nat.mul_succ]

lemma rippleSub_length {n k : ℕ} (w : SubWires n k) :
    (rippleSub w).length = 7 * k :=
  rippleSubGo_length w k le_rfl

lemma rippleSubStep_spec {n k : ℕ} (w : SubWires n k) (j : ℕ) (hj : j < k) (q : Qubits n)
    (hDj : q (w.D j) = false) (hBrj : q (w.Br (j + 1)) = false) :
    let q' := evalRevList (rippleSubStep w j hj) q
    (∀ z : Fin n, z ≠ w.D j → z ≠ w.Br (j + 1) → q' z = q z) ∧
      (q' (w.D j)).toNat + (q (w.Y j)).toNat + (q (w.Br j)).toNat =
        (q (w.X j)).toNat + 2 * (q' (w.Br (j + 1))).toNat := by
  intro q'
  have h1 : w.X j ≠ w.Y j := w.XY j hj j hj
  have h2 : w.X j ≠ w.D j := w.XD j hj j hj
  have h3 : w.X j ≠ w.Br j := w.XBr j hj j (Nat.le_of_lt hj)
  have h4 : w.X j ≠ w.Br (j + 1) := w.XBr j hj (j + 1) hj
  have h5 : w.Y j ≠ w.D j := w.YD j hj j hj
  have h6 : w.Y j ≠ w.Br j := w.YBr j hj j (Nat.le_of_lt hj)
  have h7 : w.Y j ≠ w.Br (j + 1) := w.YBr j hj (j + 1) hj
  have h8 : w.D j ≠ w.Br j := w.DBr j hj j (Nat.le_of_lt hj)
  have h9 : w.D j ≠ w.Br (j + 1) := w.DBr j hj (j + 1) hj
  have h10 : w.Br j ≠ w.Br (j + 1) := fun h => by
    have := w.Br_inj j (Nat.le_of_lt hj) (j + 1) hj h; omega
  have hD : q' (w.D j) = xor (xor (q (w.X j)) (q (w.Y j))) (q (w.Br j)) := by
    simp only [q', rippleSubStep, evalRevList_cons, evalRevList_nil,
      evalRev_cnot, evalRev_x, evalRev_ccx]
    cases hx : q (w.X j) <;> cases hy : q (w.Y j) <;> cases hbr : q (w.Br j) <;>
      simp [hDj, hBrj, hy, hbr, h5, h7, h9, h10, h8.symm, h9.symm]
  have hB : q' (w.Br (j + 1)) =
      xor ((!(q (w.X j))) && q (w.Y j)) (q (w.Br j) && !(xor (q (w.X j)) (q (w.Y j)))) := by
    simp only [q', rippleSubStep, evalRevList_cons, evalRevList_nil,
      evalRev_cnot, evalRev_x, evalRev_ccx]
    cases hx : q (w.X j) <;> cases hy : q (w.Y j) <;> cases hbr : q (w.Br j) <;>
      simp [hDj, hBrj, hy, hbr, h5, h7, h9, h10, h8.symm, h9.symm]
  refine ⟨?_, ?_⟩
  · intro z hzD hzBr
    simp only [q', rippleSubStep, evalRevList_cons, evalRevList_nil,
      evalRev_cnot, evalRev_x, evalRev_ccx]
    simp [hzD, hzBr]
  · rw [hD, hB]
    cases q (w.X j) <;> cases q (w.Y j) <;> cases q (w.Br j) <;> decide

lemma rippleSubGo_spec {n k : ℕ} (w : SubWires n k) :
    ∀ m (hm : m ≤ k) (q : Qubits n),
      (∀ t < m, q (w.D t) = false) → (∀ t, 1 ≤ t → t ≤ m → q (w.Br t) = false) →
      let q' := evalRevList (rippleSubGo w m hm) q
      (∀ z : Fin n, (∀ t < m, z ≠ w.D t) → (∀ t, 1 ≤ t → t ≤ m → z ≠ w.Br t) → q' z = q z) ∧
        regVal q' w.D m + regVal q w.Y m + (q (w.Br 0)).toNat =
          regVal q w.X m + (q' (w.Br m)).toNat * 2 ^ m
  | 0, _, q, _, _ => by
    refine ⟨fun z _ _ => rfl, ?_⟩
    simp [rippleSubGo, regVal]
  | m + 1, hm, q, hD, hBr => by
    have hm' : m ≤ k := Nat.le_of_lt hm
    have ih := rippleSubGo_spec w m hm' q (fun t ht => hD t (by omega))
      (fun t ht1 ht2 => hBr t ht1 (by omega))
    set q₁ := evalRevList (rippleSubGo w m hm') q
    have hq₁_frame : ∀ z : Fin n, (∀ t < m, z ≠ w.D t) → (∀ t, 1 ≤ t → t ≤ m → z ≠ w.Br t) →
        q₁ z = q z := ih.1
    have hq₁_arith : regVal q₁ w.D m + regVal q w.Y m + (q (w.Br 0)).toNat =
        regVal q w.X m + (q₁ (w.Br m)).toNat * 2 ^ m := ih.2
    have hDm : q₁ (w.D m) = false := by
      rw [hq₁_frame (w.D m) (fun t ht heq => by have := w.D_inj m hm t (by omega) heq; omega)
        (fun t _ ht heq => w.DBr m hm t (by omega) heq)]
      exact hD m (Nat.lt_succ_self m)
    have hBrm1 : q₁ (w.Br (m + 1)) = false := by
      rw [hq₁_frame (w.Br (m + 1)) (fun t ht heq => w.DBr t (by omega) (m + 1) hm heq.symm)
        (fun t _ ht heq => by have := w.Br_inj (m + 1) hm t (by omega) heq; omega)]
      exact hBr (m + 1) (by omega) (le_refl _)
    have hstep := rippleSubStep_spec w m hm q₁ hDm hBrm1
    set q₂ := evalRevList (rippleSubStep w m hm) q₁
    have hq₂_eq : evalRevList (rippleSubGo w (m + 1) hm) q = q₂ := by
      simp [rippleSubGo, evalRevList_append, q₁, q₂]
    rw [hq₂_eq]
    refine ⟨?_, ?_⟩
    · intro z hzD hzBr
      have hzDm : z ≠ w.D m := hzD m (Nat.lt_succ_self m)
      have hzBrm1 : z ≠ w.Br (m + 1) := hzBr (m + 1) (by omega) (le_refl _)
      rw [hstep.1 z hzDm hzBrm1]
      exact hq₁_frame z (fun t ht => hzD t (by omega)) (fun t ht1 ht2 => hzBr t ht1 (by omega))
    · have hD_eq : regVal q₂ w.D m = regVal q₁ w.D m := by
        apply regVal_eq_of_eq
        intro t ht
        exact hstep.1 (w.D t) (fun heq => by have := w.D_inj t (by omega) m hm heq; omega)
          (w.DBr t (by omega) (m + 1) hm)
      have hXm_eq : q₁ (w.X m) = q (w.X m) :=
        hq₁_frame (w.X m) (fun t ht => w.XD m hm t (by omega)) (fun t _ ht => w.XBr m hm t (by omega))
      have hYm_eq : q₁ (w.Y m) = q (w.Y m) :=
        hq₁_frame (w.Y m) (fun t ht => w.YD m hm t (by omega)) (fun t _ ht => w.YBr m hm t (by omega))
      rw [regVal_succ q₂ w.D m, hD_eq, regVal_succ q w.X m, regVal_succ q w.Y m, pow_succ]
      have hs := hstep.2
      rw [hXm_eq, hYm_eq] at hs
      have hm_mul := congrArg (· * 2 ^ m) hs
      nlinarith

lemma rippleSub_spec {n k : ℕ} (w : SubWires n k) (q : Qubits n)
    (hD : ∀ t < k, q (w.D t) = false) (hBr : ∀ t ≤ k, q (w.Br t) = false) :
    let q' := evalRevList (rippleSub w) q
    (∀ z : Fin n, (∀ t < k, z ≠ w.D t) → (∀ t, 1 ≤ t → t ≤ k → z ≠ w.Br t) → q' z = q z) ∧
      q' (w.Br k) = decide (regVal q w.X k < regVal q w.Y k) ∧
      (regVal q w.Y k ≤ regVal q w.X k → regVal q' w.D k = regVal q w.X k - regVal q w.Y k) := by
  have h := rippleSubGo_spec w k le_rfl q hD (fun t _ ht2 => hBr t ht2)
  have hBr0 : q (w.Br 0) = false := hBr 0 (Nat.zero_le k)
  simp only [hBr0, Bool.toNat_false, add_zero] at h
  change (∀ z : Fin n, (∀ t < k, z ≠ w.D t) → (∀ t, 1 ≤ t → t ≤ k → z ≠ w.Br t) →
      evalRevList (rippleSub w) q z = q z) ∧
    regVal (evalRevList (rippleSub w) q) w.D k + regVal q w.Y k =
      regVal q w.X k + (evalRevList (rippleSub w) q (w.Br k)).toNat * 2 ^ k at h
  have hltD : regVal (evalRevList (rippleSub w) q) w.D k < 2 ^ k := regVal_lt _ _ _
  have hltX : regVal q w.X k < 2 ^ k := regVal_lt _ _ _
  have hltY : regVal q w.Y k < 2 ^ k := regVal_lt _ _ _
  have hpow_pos : 0 < 2 ^ k := by positivity
  refine ⟨h.1, ?_, ?_⟩
  · by_cases hxy : regVal q w.X k < regVal q w.Y k
    · rw [decide_eq_true hxy]
      cases hbk : evalRevList (rippleSub w) q (w.Br k)
      · simp [hbk] at h
        omega
      · rfl
    · rw [decide_eq_false hxy]
      cases hbk : evalRevList (rippleSub w) q (w.Br k)
      · rfl
      · simp [hbk] at h
        omega
  · intro hle
    cases hbk : evalRevList (rippleSub w) q (w.Br k)
    · simp [hbk] at h
      omega
    · simp [hbk] at h
      omega

def gateAvoids {n : ℕ} (P : Fin n → Prop) : RevGate n → Prop
  | .x i => ¬ P i
  | .cnot c t _ => ¬ P c ∧ ¬ P t
  | .ccx a b t _ _ _ => ¬ P a ∧ ¬ P b ∧ ¬ P t

lemma evalRev_update_comm {n : ℕ} (P : Fin n → Prop) (g : RevGate n) (hg : gateAvoids P g)
    (q₁ q₂ : Qubits n) (hagree : ∀ z, ¬ P z → q₁ z = q₂ z) :
    (∀ z, ¬ P z → evalRev g q₁ z = evalRev g q₂ z) ∧ (∀ z, P z → evalRev g q₂ z = q₂ z) := by
  cases g with
  | x i =>
    have hi : ¬ P i := hg
    constructor
    · intro z hz
      by_cases hzi : z = i
      · subst hzi; simp [hagree z hz]
      · simp [hzi, hagree z hz]
    · intro z hz
      have hne : z ≠ i := fun h => by subst h; exact hi hz
      simp [hne]
  | cnot c t hct =>
    have hc : ¬ P c := hg.1
    have ht : ¬ P t := hg.2
    constructor
    · intro z hz
      by_cases hzt : z = t
      · rw [hzt, evalRev_cnot, evalRev_cnot, Function.update_self, Function.update_self,
          hagree c hc, hagree t ht]
      · simp [hzt, hagree z hz]
    · intro z hz
      have hne : z ≠ t := fun h => by subst h; exact ht hz
      simp [hne]
  | ccx a b t hab hat hbt =>
    have ha : ¬ P a := hg.1
    have hb : ¬ P b := hg.2.1
    have ht : ¬ P t := hg.2.2
    constructor
    · intro z hz
      by_cases hzt : z = t
      · rw [hzt, evalRev_ccx, evalRev_ccx, Function.update_self, Function.update_self,
          hagree a ha, hagree b hb, hagree t ht]
      · simp [hzt, hagree z hz]
    · intro z hz
      have hne : z ≠ t := fun h => by subst h; exact ht hz
      simp [hne]

lemma evalRevList_update_comm {n : ℕ} (P : Fin n → Prop) (c : List (RevGate n))
    (hc : ∀ g ∈ c, gateAvoids P g) (q₁ q₂ : Qubits n)
    (hagree : ∀ z, ¬ P z → q₁ z = q₂ z) :
    (∀ z, ¬ P z → evalRevList c q₁ z = evalRevList c q₂ z) ∧
      (∀ z, P z → evalRevList c q₂ z = q₂ z) := by
  induction c generalizing q₁ q₂ with
  | nil =>
    exact ⟨hagree, fun _ _ => rfl⟩
  | cons g gs ih =>
    have hg : gateAvoids P g := hc g (by simp)
    have hgs : ∀ g' ∈ gs, gateAvoids P g' := fun g' hg' => hc g' (by simp [hg'])
    have hstep := evalRev_update_comm P g hg q₁ q₂ hagree
    have ih' := ih hgs (evalRev g q₁) (evalRev g q₂) hstep.1
    refine ⟨ih'.1, fun z hz => ?_⟩
    rw [evalRevList_cons, ih'.2 z hz, hstep.2 z hz]

def initNatGo {n : ℕ} (M : ℕ) (X : ℕ → Fin n) : ℕ → List (RevGate n)
  | 0 => []
  | m + 1 => initNatGo M X m ++ (if M.testBit m then [.x (X m)] else [])

def initNat {n : ℕ} (M k : ℕ) (X : ℕ → Fin n) : List (RevGate n) :=
  initNatGo M X k

lemma initNatGo_length {n : ℕ} (M : ℕ) (X : ℕ → Fin n) :
    ∀ m, (initNatGo M X m).length ≤ m
  | 0 => le_refl 0
  | m + 1 => by
    have ih := initNatGo_length M X m
    simp only [initNatGo, List.length_append]
    split_ifs <;> simp <;> omega

lemma initNat_length {n : ℕ} (M k : ℕ) (X : ℕ → Fin n) :
    (initNat M k X).length ≤ k :=
  initNatGo_length M X k

lemma initNat_avoid {n : ℕ} (P : Fin n → Prop) (M k : ℕ) (X : ℕ → Fin n)
    (hX : ∀ j < k, ¬ P (X j)) : ∀ g ∈ initNat M k X, gateAvoids P g := by
  unfold initNat
  have go : ∀ m ≤ k, ∀ g ∈ initNatGo M X m, gateAvoids P g := by
    intro m hm
    induction m with
    | zero => intro g hg; simp [initNatGo] at hg
    | succ m ih =>
      intro g hg
      simp only [initNatGo, List.mem_append] at hg
      rcases hg with hg | hg
      · exact ih (by omega) g hg
      · split_ifs at hg
        · simp only [List.mem_singleton] at hg
          subst hg
          exact hX m hm
        · simp at hg
  exact go k le_rfl

lemma initNatGo_spec {n : ℕ} (M : ℕ) (X : ℕ → Fin n) :
    ∀ m (_ : ∀ i < m, ∀ j < m, X i = X j → i = j) (q : Qubits n),
      (∀ z : Fin n, (∀ j < m, z ≠ X j) → evalRevList (initNatGo M X m) q z = q z) ∧
        (∀ j < m, evalRevList (initNatGo M X m) q (X j) = xor (q (X j)) (M.testBit j))
  | 0, _, q => ⟨fun _ _ => rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | m + 1, hX, q => by
    have ih := initNatGo_spec M X m (fun i hi j hj => hX i (by omega) j (by omega)) q
    set q₁ := evalRevList (initNatGo M X m) q
    have hq₁_eq : evalRevList (initNatGo M X (m + 1)) q =
        evalRevList (if M.testBit m then [.x (X m)] else []) q₁ := by
      simp [initNatGo, evalRevList_append, q₁]
    rw [hq₁_eq]
    constructor
    · intro z hz
      have hzm : z ≠ X m := hz m (Nat.lt_succ_self m)
      have h1 : q₁ z = q z := ih.1 z (fun j hj => hz j (by omega))
      split_ifs <;> simp [hzm, h1]
    · intro j hj
      by_cases hjm : j = m
      · subst hjm
        have h1 : q₁ (X j) = q (X j) := ih.1 (X j) (fun i hi heq => by
          have := hX i (by omega) j (Nat.lt_succ_self j) heq.symm; omega)
        cases hb : M.testBit j
        · simp [h1]
        · simp [h1]
      · have hj' : j < m := by omega
        have hne : X j ≠ X m := fun heq => by
          have := hX j (by omega) m (Nat.lt_succ_self m) heq; omega
        have h1 := ih.2 j hj'
        split_ifs <;> simp [hne, h1]

lemma initNat_spec {n : ℕ} (M k : ℕ) (X : ℕ → Fin n)
    (hX : ∀ i < k, ∀ j < k, X i = X j → i = j) (q : Qubits n) :
    (∀ z : Fin n, (∀ j < k, z ≠ X j) → evalRevList (initNat M k X) q z = q z) ∧
      (∀ j < k, evalRevList (initNat M k X) q (X j) = xor (q (X j)) (M.testBit j)) :=
  initNatGo_spec M X k hX q

def ccxLoopGo {n k : ℕ} (ctrl : Fin n) (src dst : ℕ → Fin n)
    (hcs : ∀ j < k, ctrl ≠ src j) (hcd : ∀ j < k, ctrl ≠ dst j)
    (hsd : ∀ j < k, src j ≠ dst j) : ∀ m ≤ k, List (RevGate n)
  | 0, _ => []
  | m + 1, hm => ccxLoopGo ctrl src dst hcs hcd hsd m (Nat.le_of_lt hm) ++
      [.ccx ctrl (src m) (dst m) (hcs m hm) (hcd m hm) (hsd m hm)]

def ccxLoop {n : ℕ} (ctrl : Fin n) (src dst : ℕ → Fin n) (k : ℕ)
    (hcs : ∀ j < k, ctrl ≠ src j) (hcd : ∀ j < k, ctrl ≠ dst j)
    (hsd : ∀ j < k, src j ≠ dst j) : List (RevGate n) :=
  ccxLoopGo ctrl src dst hcs hcd hsd k le_rfl

lemma ccxLoopGo_length {n k : ℕ} (ctrl : Fin n) (src dst : ℕ → Fin n)
    (hcs : ∀ j < k, ctrl ≠ src j) (hcd : ∀ j < k, ctrl ≠ dst j)
    (hsd : ∀ j < k, src j ≠ dst j) :
    ∀ m (hm : m ≤ k), (ccxLoopGo ctrl src dst hcs hcd hsd m hm).length = m
  | 0, _ => rfl
  | m + 1, hm => by
    rw [ccxLoopGo, List.length_append, ccxLoopGo_length ctrl src dst hcs hcd hsd m (Nat.le_of_lt hm)]
    rfl

lemma ccxLoop_length {n : ℕ} (ctrl : Fin n) (src dst : ℕ → Fin n) (k : ℕ)
    (hcs : ∀ j < k, ctrl ≠ src j) (hcd : ∀ j < k, ctrl ≠ dst j)
    (hsd : ∀ j < k, src j ≠ dst j) :
    (ccxLoop ctrl src dst k hcs hcd hsd).length = k :=
  ccxLoopGo_length ctrl src dst hcs hcd hsd k le_rfl

lemma ccxLoopGo_avoid {n k : ℕ} (P : Fin n → Prop) (ctrl : Fin n) (src dst : ℕ → Fin n)
    (hcs : ∀ j < k, ctrl ≠ src j) (hcd : ∀ j < k, ctrl ≠ dst j)
    (hsd : ∀ j < k, src j ≠ dst j)
    (hc : ¬ P ctrl) (hs : ∀ j < k, ¬ P (src j)) (hd : ∀ j < k, ¬ P (dst j)) :
    ∀ m (hm : m ≤ k), ∀ g ∈ ccxLoopGo ctrl src dst hcs hcd hsd m hm, gateAvoids P g
  | 0, _, _, hg => by simp [ccxLoopGo] at hg
  | m + 1, hm, g, hg => by
    simp only [ccxLoopGo, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ccxLoopGo_avoid P ctrl src dst hcs hcd hsd hc hs hd m (Nat.le_of_lt hm) g hg
    · exact ⟨hc, hs m hm, hd m hm⟩

lemma ccxLoop_avoid {n : ℕ} (P : Fin n → Prop) (ctrl : Fin n) (src dst : ℕ → Fin n) (k : ℕ)
    (hcs : ∀ j < k, ctrl ≠ src j) (hcd : ∀ j < k, ctrl ≠ dst j)
    (hsd : ∀ j < k, src j ≠ dst j)
    (hc : ¬ P ctrl) (hs : ∀ j < k, ¬ P (src j)) (hd : ∀ j < k, ¬ P (dst j)) :
    ∀ g ∈ ccxLoop ctrl src dst k hcs hcd hsd, gateAvoids P g :=
  ccxLoopGo_avoid P ctrl src dst hcs hcd hsd hc hs hd k le_rfl

lemma ccxLoopGo_spec {n k : ℕ} (ctrl : Fin n) (src dst : ℕ → Fin n)
    (hcs : ∀ j < k, ctrl ≠ src j) (hcd : ∀ j < k, ctrl ≠ dst j)
    (hsd : ∀ i < k, ∀ j < k, src i ≠ dst j)
    (hd_inj : ∀ i < k, ∀ j < k, dst i = dst j → i = j) :
    ∀ m (hm : m ≤ k) (q : Qubits n),
      (∀ z : Fin n, (∀ j < m, z ≠ dst j) →
        evalRevList (ccxLoopGo ctrl src dst hcs hcd (fun j hj => hsd j hj j hj) m hm) q z = q z) ∧
      (∀ j < m, evalRevList (ccxLoopGo ctrl src dst hcs hcd (fun j hj => hsd j hj j hj) m hm) q (dst j) =
        xor (q (dst j)) (q ctrl && q (src j)))
  | 0, _, q => ⟨fun _ _ => rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | m + 1, hm, q => by
    have ih := ccxLoopGo_spec ctrl src dst hcs hcd hsd hd_inj m (Nat.le_of_lt hm) q
    set q₁ := evalRevList (ccxLoopGo ctrl src dst hcs hcd (fun j hj => hsd j hj j hj) m (Nat.le_of_lt hm)) q
    have hq₁_eq : evalRevList (ccxLoopGo ctrl src dst hcs hcd (fun j hj => hsd j hj j hj) (m + 1) hm) q =
        evalRev (.ccx ctrl (src m) (dst m) (hcs m hm) (hcd m hm) (hsd m hm m hm)) q₁ := by
      simp [ccxLoopGo, evalRevList_append, q₁]
    rw [hq₁_eq]
    have hctrl : q₁ ctrl = q ctrl := ih.1 ctrl (fun j hj => (hcd j (by omega)))
    have hsrc : q₁ (src m) = q (src m) := ih.1 (src m) (fun j hj => hsd m hm j (by omega))
    constructor
    · intro z hz
      have hzm : z ≠ dst m := hz m (Nat.lt_succ_self m)
      rw [evalRev_ccx, Function.update_of_ne hzm]
      exact ih.1 z (fun j hj => hz j (by omega))
    · intro j hj
      by_cases hjm : j = m
      · subst hjm
        have hdj : q₁ (dst j) = q (dst j) := ih.1 (dst j) (fun i hi heq => by
          have := hd_inj j hm i (by omega) heq; omega)
        simp only [evalRev_ccx, Function.update_self, hctrl, hsrc, hdj]
      · have hj' : j < m := by omega
        have hne : dst j ≠ dst m := fun heq => by
          have := hd_inj j (by omega) m hm heq; omega
        rw [evalRev_ccx, Function.update_of_ne hne]
        exact ih.2 j hj'

lemma ccxLoop_spec {n : ℕ} (ctrl : Fin n) (src dst : ℕ → Fin n) (k : ℕ)
    (hcs : ∀ j < k, ctrl ≠ src j) (hcd : ∀ j < k, ctrl ≠ dst j)
    (hsd : ∀ i < k, ∀ j < k, src i ≠ dst j)
    (hd_inj : ∀ i < k, ∀ j < k, dst i = dst j → i = j) (q : Qubits n) :
    let q' := evalRevList (ccxLoop ctrl src dst k hcs hcd (fun j hj => hsd j hj j hj)) q
    (∀ z : Fin n, (∀ j < k, z ≠ dst j) → q' z = q z) ∧
      (∀ j < k, q' (dst j) = xor (q (dst j)) (q ctrl && q (src j))) :=
  ccxLoopGo_spec ctrl src dst hcs hcd hsd hd_inj k le_rfl q

def swapLoopGo {n k : ℕ} (A B : ℕ → Fin n) (hAB : ∀ j < k, A j ≠ B j) :
    ∀ m ≤ k, List (RevGate n)
  | 0, _ => []
  | m + 1, hm => swapLoopGo A B hAB m (Nat.le_of_lt hm) ++ swapRev (A m) (B m) (hAB m hm)

def swapLoop {n : ℕ} (A B : ℕ → Fin n) (k : ℕ) (hAB : ∀ j < k, A j ≠ B j) : List (RevGate n) :=
  swapLoopGo A B hAB k le_rfl

lemma swapLoopGo_length {n k : ℕ} (A B : ℕ → Fin n) (hAB : ∀ j < k, A j ≠ B j) :
    ∀ m (hm : m ≤ k), (swapLoopGo A B hAB m hm).length = 3 * m
  | 0, _ => rfl
  | m + 1, hm => by
    rw [swapLoopGo, List.length_append, swapLoopGo_length A B hAB m (Nat.le_of_lt hm)]
    simp [swapRev, Nat.mul_succ]

lemma swapLoop_length {n : ℕ} (A B : ℕ → Fin n) (k : ℕ) (hAB : ∀ j < k, A j ≠ B j) :
    (swapLoop A B k hAB).length = 3 * k :=
  swapLoopGo_length A B hAB k le_rfl

lemma swapLoopGo_spec {n k : ℕ} (A B : ℕ → Fin n)
    (hA : ∀ i < k, ∀ j < k, A i = A j → i = j)
    (hB : ∀ i < k, ∀ j < k, B i = B j → i = j)
    (hAB : ∀ i < k, ∀ j < k, A i ≠ B j) :
    ∀ m (hm : m ≤ k) (q : Qubits n),
      (∀ z : Fin n, (∀ j < m, z ≠ A j ∧ z ≠ B j) →
        evalRevList (swapLoopGo A B (fun j hj => hAB j hj j hj) m hm) q z = q z) ∧
      (∀ j < m, evalRevList (swapLoopGo A B (fun j hj => hAB j hj j hj) m hm) q (A j) = q (B j) ∧
        evalRevList (swapLoopGo A B (fun j hj => hAB j hj j hj) m hm) q (B j) = q (A j))
  | 0, _, q => ⟨fun _ _ => rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | m + 1, hm, q => by
    have ih := swapLoopGo_spec A B hA hB hAB m (Nat.le_of_lt hm) q
    set q₁ := evalRevList (swapLoopGo A B (fun j hj => hAB j hj j hj) m (Nat.le_of_lt hm)) q
    have hq₁_eq : evalRevList (swapLoopGo A B (fun j hj => hAB j hj j hj) (m + 1) hm) q =
        Function.update (Function.update q₁ (A m) (q₁ (B m))) (B m) (q₁ (A m)) := by
      simp [swapLoopGo, evalRevList_append, evalRevList_swapRev, q₁]
    rw [hq₁_eq]
    have hAm : q₁ (A m) = q (A m) :=
      ih.1 (A m) (fun j hj => ⟨fun heq => by have := hA m hm j (by omega) heq; omega,
        hAB m hm j (by omega)⟩)
    have hBm : q₁ (B m) = q (B m) :=
      ih.1 (B m) (fun j hj => ⟨(hAB j (by omega) m hm).symm,
        fun heq => by have := hB m hm j (by omega) heq; omega⟩)
    constructor
    · intro z hz
      have hzAm : z ≠ A m := (hz m (Nat.lt_succ_self m)).1
      have hzBm : z ≠ B m := (hz m (Nat.lt_succ_self m)).2
      rw [Function.update_of_ne hzBm, Function.update_of_ne hzAm]
      exact ih.1 z (fun j hj => hz j (by omega))
    · intro j hj
      by_cases hjm : j = m
      · rw [hjm]
        have hne : A m ≠ B m := hAB m hm m hm
        rw [Function.update_of_ne hne, Function.update_self, Function.update_self, hAm, hBm]
        exact ⟨rfl, rfl⟩
      · have hj' : j < m := by omega
        have hAjAm : A j ≠ A m := fun heq => by have := hA j (by omega) m hm heq; omega
        have hAjBm : A j ≠ B m := hAB j (by omega) m hm
        have hBjAm : B j ≠ A m := (hAB m hm j (by omega)).symm
        have hBjBm : B j ≠ B m := fun heq => by have := hB j (by omega) m hm heq; omega
        rw [Function.update_of_ne hAjBm, Function.update_of_ne hAjAm,
          Function.update_of_ne hBjBm, Function.update_of_ne hBjAm]
        exact ih.2 j hj'

lemma swapLoop_spec {n : ℕ} (A B : ℕ → Fin n) (k : ℕ)
    (hA : ∀ i < k, ∀ j < k, A i = A j → i = j)
    (hB : ∀ i < k, ∀ j < k, B i = B j → i = j)
    (hAB : ∀ i < k, ∀ j < k, A i ≠ B j) (q : Qubits n) :
    let q' := evalRevList (swapLoop A B k (fun j hj => hAB j hj j hj)) q
    (∀ z : Fin n, (∀ j < k, z ≠ A j ∧ z ≠ B j) → q' z = q z) ∧
      (∀ j < k, q' (A j) = q (B j) ∧ q' (B j) = q (A j)) :=
  swapLoopGo_spec A B hA hB hAB k le_rfl q

def fbOutW_raw (r L : ℕ) : ℕ :=
  3 * ((r + 1) * L) + 13 * L + 12

def base_raw (r L : ℕ) : ℕ :=
  3 * ((r + 1) * L)

lemma two_L_le_W (r L : ℕ) (hr : 1 ≤ r) : 2 * L ≤ (r + 1) * L := by
  nlinarith

lemma five_L_le_three_W (r L : ℕ) (hr : 1 ≤ r) : 5 * L ≤ 3 * ((r + 1) * L) := by
  nlinarith

def w0_w (r L : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨0, by simp [fbOutW_raw]⟩

def regA_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨L + min j L, by simp only [fbOutW_raw]; nlinarith [Nat.min_le_right j L]⟩

def wW_w (r L : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨(r + 1) * L, by simp only [fbOutW_raw]; nlinarith⟩

def regB_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨(r + 1) * L + L + min j L, by simp only [fbOutW_raw]; nlinarith [Nat.min_le_right j L]⟩

def wireF_w (r L : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨2 * ((r + 1) * L), by simp only [fbOutW_raw]; nlinarith⟩

def regH_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨2 * ((r + 1) * L) + L + min j L, by simp only [fbOutW_raw]; nlinarith [Nat.min_le_right j L]⟩

def out0_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + min j L, by simp only [fbOutW_raw, base_raw]; omega⟩

def out1_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + L + min j L, by simp only [fbOutW_raw, base_raw]; omega⟩

def out2_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 2 * L + min j L, by simp only [fbOutW_raw, base_raw]; omega⟩

def out3_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 3 * L + min j L, by simp only [fbOutW_raw, base_raw]; omega⟩

def out4_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 4 * L + min j L, by simp only [fbOutW_raw, base_raw]; omega⟩

def outAll_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + min j (5 * L), by simp only [fbOutW_raw, base_raw]; omega⟩

def lowAll_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨min j (5 * L), by simp only [fbOutW_raw]; nlinarith [Nat.min_le_right j (5 * L)]⟩

def tmp_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 5 * L + min j L, by simp only [fbOutW_raw, base_raw]; omega⟩

def regM_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 6 * L + min j L, by simp only [fbOutW_raw, base_raw]; omega⟩

def regS_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 7 * L + 1 + min j L, by simp only [fbOutW_raw, base_raw]; omega⟩

def regC_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 8 * L + 2 + min j (L + 1), by simp only [fbOutW_raw, base_raw]; omega⟩

def regD1_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 9 * L + 4 + min j L, by simp only [fbOutW_raw, base_raw]; omega⟩

def regBr1_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 10 * L + 5 + min j (L + 1), by simp only [fbOutW_raw, base_raw]; omega⟩

def regD2_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 11 * L + 7 + min j L, by simp only [fbOutW_raw, base_raw]; omega⟩

def regBr2_w (r L j : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 12 * L + 8 + min j (L + 1), by simp only [fbOutW_raw, base_raw]; omega⟩

def zA_w (r L : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 13 * L + 10, by simp only [fbOutW_raw, base_raw]; omega⟩

def zB_w (r L : ℕ) : Fin (fbOutW_raw r L) :=
  ⟨base_raw r L + 13 * L + 11, by simp only [fbOutW_raw, base_raw]; omega⟩

def InScratch (r L : ℕ) (z : Fin (fbOutW_raw r L)) : Prop :=
  base_raw r L + 6 * L ≤ z.val ∧ z.val < base_raw r L + 13 * L + 10

lemma regM_inScratch {r L j : ℕ} : InScratch r L (regM_w r L j) := by
  simp only [InScratch, regM_w]; omega

lemma regS_inScratch {r L j : ℕ} : InScratch r L (regS_w r L j) := by
  simp only [InScratch, regS_w]; omega

lemma regC_inScratch {r L j : ℕ} : InScratch r L (regC_w r L j) := by
  simp only [InScratch, regC_w]; omega

lemma regD1_inScratch {r L j : ℕ} : InScratch r L (regD1_w r L j) := by
  simp only [InScratch, regD1_w]; omega

lemma regBr1_inScratch {r L j : ℕ} : InScratch r L (regBr1_w r L j) := by
  simp only [InScratch, regBr1_w]; omega

lemma regD2_inScratch {r L j : ℕ} : InScratch r L (regD2_w r L j) := by
  simp only [InScratch, regD2_w]; omega

lemma regBr2_inScratch {r L j : ℕ} : InScratch r L (regBr2_w r L j) := by
  simp only [InScratch, regBr2_w]; omega

lemma regM_inj {r L i j : ℕ} (hi : i < L + 1) (hj : j < L + 1)
    (heq : regM_w r L i = regM_w r L j) : i = j := by
  simp only [regM_w, Fin.ext_iff] at heq
  rw [min_eq_left (by omega), min_eq_left (by omega)] at heq
  omega

lemma regS_inj {r L i j : ℕ} (hi : i < L + 1) (hj : j < L + 1)
    (heq : regS_w r L i = regS_w r L j) : i = j := by
  simp only [regS_w, Fin.ext_iff] at heq
  rw [min_eq_left (by omega), min_eq_left (by omega)] at heq
  omega

lemma regC_inj {r L i j : ℕ} (hi : i ≤ L + 1) (hj : j ≤ L + 1)
    (heq : regC_w r L i = regC_w r L j) : i = j := by
  simp only [regC_w, Fin.ext_iff] at heq
  rw [min_eq_left hi, min_eq_left hj] at heq
  omega

lemma regD1_inj {r L i j : ℕ} (hi : i < L + 1) (hj : j < L + 1)
    (heq : regD1_w r L i = regD1_w r L j) : i = j := by
  simp only [regD1_w, Fin.ext_iff] at heq
  rw [min_eq_left (by omega), min_eq_left (by omega)] at heq
  omega

lemma regBr1_inj {r L i j : ℕ} (hi : i ≤ L + 1) (hj : j ≤ L + 1)
    (heq : regBr1_w r L i = regBr1_w r L j) : i = j := by
  simp only [regBr1_w, Fin.ext_iff] at heq
  rw [min_eq_left hi, min_eq_left hj] at heq
  omega

lemma regD2_inj {r L i j : ℕ} (hi : i < L + 1) (hj : j < L + 1)
    (heq : regD2_w r L i = regD2_w r L j) : i = j := by
  simp only [regD2_w, Fin.ext_iff] at heq
  rw [min_eq_left (by omega), min_eq_left (by omega)] at heq
  omega

lemma regBr2_inj {r L i j : ℕ} (hi : i ≤ L + 1) (hj : j ≤ L + 1)
    (heq : regBr2_w r L i = regBr2_w r L j) : i = j := by
  simp only [regBr2_w, Fin.ext_iff] at heq
  rw [min_eq_left hi, min_eq_left hj] at heq
  omega

lemma regM_ne_regS {r L i j : ℕ} : regM_w r L i ≠ regS_w r L j := by
  intro heq; simp only [regM_w, regS_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regM_ne_regC {r L i j : ℕ} : regM_w r L i ≠ regC_w r L j := by
  intro heq; simp only [regM_w, regC_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regM_ne_regD1 {r L i j : ℕ} : regM_w r L i ≠ regD1_w r L j := by
  intro heq; simp only [regM_w, regD1_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regM_ne_regBr1 {r L i j : ℕ} : regM_w r L i ≠ regBr1_w r L j := by
  intro heq; simp only [regM_w, regBr1_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regM_ne_regD2 {r L i j : ℕ} : regM_w r L i ≠ regD2_w r L j := by
  intro heq; simp only [regM_w, regD2_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regM_ne_regBr2 {r L i j : ℕ} : regM_w r L i ≠ regBr2_w r L j := by
  intro heq; simp only [regM_w, regBr2_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regS_ne_regC {r L i j : ℕ} : regS_w r L i ≠ regC_w r L j := by
  intro heq; simp only [regS_w, regC_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regS_ne_regD1 {r L i j : ℕ} : regS_w r L i ≠ regD1_w r L j := by
  intro heq; simp only [regS_w, regD1_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regS_ne_regBr1 {r L i j : ℕ} : regS_w r L i ≠ regBr1_w r L j := by
  intro heq; simp only [regS_w, regBr1_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regS_ne_regD2 {r L i j : ℕ} : regS_w r L i ≠ regD2_w r L j := by
  intro heq; simp only [regS_w, regD2_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regS_ne_regBr2 {r L i j : ℕ} : regS_w r L i ≠ regBr2_w r L j := by
  intro heq; simp only [regS_w, regBr2_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regC_ne_regD1 {r L i j : ℕ} : regC_w r L i ≠ regD1_w r L j := by
  intro heq; simp only [regC_w, regD1_w, Fin.ext_iff] at heq; have := Nat.min_le_right i (L + 1); omega
lemma regC_ne_regBr1 {r L i j : ℕ} : regC_w r L i ≠ regBr1_w r L j := by
  intro heq; simp only [regC_w, regBr1_w, Fin.ext_iff] at heq; have := Nat.min_le_right i (L + 1); omega
lemma regC_ne_regD2 {r L i j : ℕ} : regC_w r L i ≠ regD2_w r L j := by
  intro heq; simp only [regC_w, regD2_w, Fin.ext_iff] at heq; have := Nat.min_le_right i (L + 1); omega
lemma regC_ne_regBr2 {r L i j : ℕ} : regC_w r L i ≠ regBr2_w r L j := by
  intro heq; simp only [regC_w, regBr2_w, Fin.ext_iff] at heq; have := Nat.min_le_right i (L + 1); omega
lemma regD1_ne_regBr1 {r L i j : ℕ} : regD1_w r L i ≠ regBr1_w r L j := by
  intro heq; simp only [regD1_w, regBr1_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regD1_ne_regD2 {r L i j : ℕ} : regD1_w r L i ≠ regD2_w r L j := by
  intro heq; simp only [regD1_w, regD2_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regD1_ne_regBr2 {r L i j : ℕ} : regD1_w r L i ≠ regBr2_w r L j := by
  intro heq; simp only [regD1_w, regBr2_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regBr1_ne_regD2 {r L i j : ℕ} : regBr1_w r L i ≠ regD2_w r L j := by
  intro heq; simp only [regBr1_w, regD2_w, Fin.ext_iff] at heq; have := Nat.min_le_right i (L + 1); omega
lemma regBr1_ne_regBr2 {r L i j : ℕ} : regBr1_w r L i ≠ regBr2_w r L j := by
  intro heq; simp only [regBr1_w, regBr2_w, Fin.ext_iff] at heq; have := Nat.min_le_right i (L + 1); omega
lemma regD2_ne_regBr2 {r L i j : ℕ} : regD2_w r L i ≠ regBr2_w r L j := by
  intro heq; simp only [regD2_w, regBr2_w, Fin.ext_iff] at heq; have := Nat.min_le_right i L; omega
lemma regBr1_ne_regS {r L i j : ℕ} : regBr1_w r L i ≠ regS_w r L j := regS_ne_regBr1.symm
lemma regBr1_ne_regD1 {r L i j : ℕ} : regBr1_w r L i ≠ regD1_w r L j := regD1_ne_regBr1.symm

lemma rippleAddGo_avoid {n k : ℕ} (w : AddWires n k) (Q : Fin n → Prop)
    (ha : ∀ j < k, ¬ Q (w.A j)) (hb : ∀ j < k, ¬ Q (w.B j))
    (hs : ∀ j < k, ¬ Q (w.S j)) (hc : ∀ j ≤ k, ¬ Q (w.C j)) :
    ∀ m (hm : m ≤ k), ∀ g ∈ rippleAddGo w m hm, gateAvoids Q g
  | 0, _, _, hg => by simp [rippleAddGo] at hg
  | m + 1, hm, g, hg => by
    simp only [rippleAddGo, List.mem_append] at hg
    rcases hg with hg | hg
    · exact rippleAddGo_avoid w Q ha hb hs hc m (Nat.le_of_lt hm) g hg
    · simp only [rippleAddStep, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact ⟨ha m hm, hs m hm⟩
      · exact ⟨hb m hm, hs m hm⟩
      · exact ⟨ha m hm, hb m hm, hc (m + 1) hm⟩
      · exact ⟨hc m (by omega), hs m hm, hc (m + 1) hm⟩
      · exact ⟨hc m (by omega), hs m hm⟩

lemma rippleAdd_avoid {n k : ℕ} (w : AddWires n k) (Q : Fin n → Prop)
    (ha : ∀ j < k, ¬ Q (w.A j)) (hb : ∀ j < k, ¬ Q (w.B j))
    (hs : ∀ j < k, ¬ Q (w.S j)) (hc : ∀ j ≤ k, ¬ Q (w.C j)) :
    ∀ g ∈ rippleAdd w, gateAvoids Q g :=
  rippleAddGo_avoid w Q ha hb hs hc k le_rfl

lemma rippleSubGo_avoid {n k : ℕ} (w : SubWires n k) (Q : Fin n → Prop)
    (hx : ∀ j < k, ¬ Q (w.X j)) (hy : ∀ j < k, ¬ Q (w.Y j))
    (hd : ∀ j < k, ¬ Q (w.D j)) (hbr : ∀ j ≤ k, ¬ Q (w.Br j)) :
    ∀ m (hm : m ≤ k), ∀ g ∈ rippleSubGo w m hm, gateAvoids Q g
  | 0, _, _, hg => by simp [rippleSubGo] at hg
  | m + 1, hm, g, hg => by
    simp only [rippleSubGo, List.mem_append] at hg
    rcases hg with hg | hg
    · exact rippleSubGo_avoid w Q hx hy hd hbr m (Nat.le_of_lt hm) g hg
    · simp only [rippleSubStep, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hx m hm, hd m hm⟩
      · exact hd m hm
      · exact ⟨hd m hm, hy m hm, hbr (m + 1) hm⟩
      · exact ⟨hy m hm, hd m hm⟩
      · exact ⟨hbr m (by omega), hd m hm, hbr (m + 1) hm⟩
      · exact hd m hm
      · exact ⟨hbr m (by omega), hd m hm⟩

lemma rippleSub_avoid {n k : ℕ} (w : SubWires n k) (Q : Fin n → Prop)
    (hx : ∀ j < k, ¬ Q (w.X j)) (hy : ∀ j < k, ¬ Q (w.Y j))
    (hd : ∀ j < k, ¬ Q (w.D j)) (hbr : ∀ j ≤ k, ¬ Q (w.Br j)) :
    ∀ g ∈ rippleSub w, gateAvoids Q g :=
  rippleSubGo_avoid w Q hx hy hd hbr k le_rfl

structure ValidModIO (r L : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L)) where
  Out_inj : ∀ i < L, ∀ j < L, Out i = Out j → i = j
  XY : ∀ i ≤ L, ∀ j ≤ L, X i ≠ Y j
  XOut : ∀ i ≤ L, ∀ j < L, X i ≠ Out j
  YOut : ∀ i ≤ L, ∀ j < L, Y i ≠ Out j
  X_ns : ∀ i ≤ L, ¬ InScratch r L (X i)
  Y_ns : ∀ i ≤ L, ¬ InScratch r L (Y i)
  Out_ns : ∀ j < L, ¬ InScratch r L (Out j)

def mkAdd_XY_S {r L : ℕ} (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) : AddWires (fbOutW_raw r L) (L + 1) where
  A := X
  B := Y
  S := regS_w r L
  C := regC_w r L
  S_inj := fun _ hi _ hj => regS_inj hi hj
  C_inj := fun _ hi _ hj => regC_inj hi hj
  AB := fun i hi j hj => h.XY i (by omega) j (by omega)
  AS := fun i hi j _ heq => h.X_ns i (by omega) (heq ▸ regS_inScratch)
  AC := fun i hi j _ heq => h.X_ns i (by omega) (heq ▸ regC_inScratch)
  BS := fun i hi j _ heq => h.Y_ns i (by omega) (heq ▸ regS_inScratch)
  BC := fun i hi j _ heq => h.Y_ns i (by omega) (heq ▸ regC_inScratch)
  SC := fun _ _ _ _ => regS_ne_regC

def mkSub_SM_D1 (r L : ℕ) : SubWires (fbOutW_raw r L) (L + 1) where
  X := regS_w r L
  Y := regM_w r L
  D := regD1_w r L
  Br := regBr1_w r L
  D_inj := fun _ hi _ hj => regD1_inj hi hj
  Br_inj := fun _ hi _ hj => regBr1_inj hi hj
  XY := fun _ _ _ _ => regM_ne_regS.symm
  XD := fun _ _ _ _ => regS_ne_regD1
  XBr := fun _ _ _ _ => regS_ne_regBr1
  YD := fun _ _ _ _ => regM_ne_regD1
  YBr := fun _ _ _ _ => regM_ne_regBr1
  DBr := fun _ _ _ _ => regD1_ne_regBr1

def mkAdd_XM_S {r L : ℕ} (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) : AddWires (fbOutW_raw r L) (L + 1) where
  A := X
  B := regM_w r L
  S := regS_w r L
  C := regC_w r L
  S_inj := fun _ hi _ hj => regS_inj hi hj
  C_inj := fun _ hi _ hj => regC_inj hi hj
  AB := fun i hi j _ heq => h.X_ns i (by omega) (heq ▸ regM_inScratch)
  AS := fun i hi j _ heq => h.X_ns i (by omega) (heq ▸ regS_inScratch)
  AC := fun i hi j _ heq => h.X_ns i (by omega) (heq ▸ regC_inScratch)
  BS := fun _ _ _ _ => regM_ne_regS
  BC := fun _ _ _ _ => regM_ne_regC
  SC := fun _ _ _ _ => regS_ne_regC

def mkSub_XY_D1 {r L : ℕ} (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) : SubWires (fbOutW_raw r L) (L + 1) where
  X := X
  Y := Y
  D := regD1_w r L
  Br := regBr1_w r L
  D_inj := fun _ hi _ hj => regD1_inj hi hj
  Br_inj := fun _ hi _ hj => regBr1_inj hi hj
  XY := fun i hi j hj => h.XY i (by omega) j (by omega)
  XD := fun i hi j _ heq => h.X_ns i (by omega) (heq ▸ regD1_inScratch)
  XBr := fun i hi j _ heq => h.X_ns i (by omega) (heq ▸ regBr1_inScratch)
  YD := fun i hi j _ heq => h.Y_ns i (by omega) (heq ▸ regD1_inScratch)
  YBr := fun i hi j _ heq => h.Y_ns i (by omega) (heq ▸ regBr1_inScratch)
  DBr := fun _ _ _ _ => regD1_ne_regBr1

def mkSub_SY_D2 {r L : ℕ} (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) : SubWires (fbOutW_raw r L) (L + 1) where
  X := regS_w r L
  Y := Y
  D := regD2_w r L
  Br := regBr2_w r L
  D_inj := fun _ hi _ hj => regD2_inj hi hj
  Br_inj := fun _ hi _ hj => regBr2_inj hi hj
  XY := fun _ _ j hj heq => h.Y_ns j (by omega) (heq ▸ regS_inScratch)
  XD := fun _ _ _ _ => regS_ne_regD2
  XBr := fun _ _ _ _ => regS_ne_regBr2
  YD := fun i hi j _ heq => h.Y_ns i (by omega) (heq ▸ regD2_inScratch)
  YBr := fun i hi j _ heq => h.Y_ns i (by omega) (heq ▸ regBr2_inScratch)
  DBr := fun _ _ _ _ => regD2_ne_regBr2

def addModMPre {r L : ℕ} (M : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) : List (RevGate (fbOutW_raw r L)) :=
  initNat M (L + 1) (regM_w r L) ++
    rippleAdd (mkAdd_XY_S X Y Out h) ++
    rippleSub (mkSub_SM_D1 r L)

def addModMCopy {r L : ℕ} (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) : List (RevGate (fbOutW_raw r L)) :=
  ccxLoop (regBr1_w r L (L + 1)) (regS_w r L) Out L
      (fun j _ heq => by simp only [regBr1_w, regS_w, Fin.ext_iff] at heq; omega)
      (fun j hj heq => h.Out_ns j hj (by rw [← heq]; exact regBr1_inScratch))
      (fun j hj heq => h.Out_ns j hj (by rw [← heq]; exact regS_inScratch)) ++
    [.x (regBr1_w r L (L + 1))] ++
    ccxLoop (regBr1_w r L (L + 1)) (regD1_w r L) Out L
      (fun j _ heq => by simp only [regBr1_w, regD1_w, Fin.ext_iff] at heq; omega)
      (fun j hj heq => h.Out_ns j hj (by rw [← heq]; exact regBr1_inScratch))
      (fun j hj heq => h.Out_ns j hj (by rw [← heq]; exact regD1_inScratch)) ++
    [.x (regBr1_w r L (L + 1))]

def addModM {r L : ℕ} (M : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) : List (RevGate (fbOutW_raw r L)) :=
  addModMPre M X Y Out h ++ addModMCopy X Y Out h ++ (addModMPre M X Y Out h).reverse

lemma addModM_length {r L : ℕ} (M : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) :
    (addModM M X Y Out h).length ≤ 28 * L + 28 := by
  have hpre : (addModMPre M X Y Out h).length ≤ 13 * L + 13 := by
    simp only [addModMPre, List.length_append, rippleAdd_length, rippleSub_length]
    have hi := initNat_length M (L + 1) (regM_w r L)
    omega
  have hcopy : (addModMCopy X Y Out h).length = 2 * L + 2 := by
    simp [addModMCopy, ccxLoop_length]; omega
  simp only [addModM, List.length_append, List.length_reverse]
  omega

lemma addModMPre_avoid_Out {r L : ℕ} (M : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) (P : Fin (fbOutW_raw r L) → Prop)
    (hPX : ∀ i ≤ L, ¬ P (X i)) (hPY : ∀ i ≤ L, ¬ P (Y i))
    (hPS : ∀ z, InScratch r L z → ¬ P z) :
    ∀ g ∈ addModMPre M X Y Out h, gateAvoids P g := by
  have hM : ∀ j < L + 1, ¬ P (regM_w r L j) := fun _ _ => hPS _ regM_inScratch
  have hS : ∀ j < L + 1, ¬ P (regS_w r L j) := fun _ _ => hPS _ regS_inScratch
  have hC : ∀ j ≤ L + 1, ¬ P (regC_w r L j) := fun _ _ => hPS _ regC_inScratch
  have hD1 : ∀ j < L + 1, ¬ P (regD1_w r L j) := fun _ _ => hPS _ regD1_inScratch
  have hBr1 : ∀ j ≤ L + 1, ¬ P (regBr1_w r L j) := fun _ _ => hPS _ regBr1_inScratch
  intro g hg
  simp only [addModMPre, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact initNat_avoid P M (L + 1) (regM_w r L) hM g hg
  · exact rippleAdd_avoid (mkAdd_XY_S X Y Out h) P
      (fun j hj => hPX j (by omega)) (fun j hj => hPY j (by omega)) hS hC g hg
  · exact rippleSub_avoid (mkSub_SM_D1 r L) P hS hM hD1 hBr1 g hg

lemma addModM_avoid {r L : ℕ} (M : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) (P : Fin (fbOutW_raw r L) → Prop)
    (hPX : ∀ i ≤ L, ¬ P (X i)) (hPY : ∀ i ≤ L, ¬ P (Y i))
    (hPOut : ∀ j < L, ¬ P (Out j)) (hPS : ∀ z, InScratch r L z → ¬ P z) :
    ∀ g ∈ addModM M X Y Out h, gateAvoids P g := by
  have hpre : ∀ g ∈ addModMPre M X Y Out h, gateAvoids P g :=
    addModMPre_avoid_Out M X Y Out h P hPX hPY hPS
  have hcopy : ∀ g ∈ addModMCopy X Y Out h, gateAvoids P g := by
    intro g hg
    simp only [addModMCopy, List.mem_append, List.mem_singleton] at hg
    rcases hg with ((hg | rfl) | hg) | rfl
    · exact ccxLoop_avoid P _ _ _ L _ _ _ (hPS _ regBr1_inScratch)
        (fun _ _ => hPS _ regS_inScratch) hPOut g hg
    · exact hPS _ regBr1_inScratch
    · exact ccxLoop_avoid P _ _ _ L _ _ _ (hPS _ regBr1_inScratch)
        (fun _ _ => hPS _ regD1_inScratch) hPOut g hg
    · exact hPS _ regBr1_inScratch
  intro g hg
  simp only [addModM, List.mem_append, List.mem_reverse] at hg
  rcases hg with (hg | hg) | hg
  · exact hpre g hg
  · exact hcopy g hg
  · exact hpre g hg

lemma addModM_spec {r L : ℕ} (M : ℕ) (_ : 1 ≤ M) (hML : M < 2 ^ L)
    (X Y Out : ℕ → Fin (fbOutW_raw r L)) (h : ValidModIO r L X Y Out)
    (q : Qubits (fbOutW_raw r L))
    (hq_scr : ∀ z, InScratch r L z → q z = false)
    (hq_out : ∀ j < L, q (Out j) = false)
    (hqX : regVal q X (L + 1) < M) (hqY : regVal q Y (L + 1) < M) :
    let q' := evalRevList (addModM M X Y Out h) q
    (∀ z, (∀ j < L, z ≠ Out j) → q' z = q z) ∧
      (∀ z, InScratch r L z → q' z = false) ∧
      (∀ j < L, q' (Out j) = ((regVal q X (L + 1) + regVal q Y (L + 1)) % M).testBit j) := by
  intro q'
  let c1 := initNat M (L + 1) (regM_w r L)
  let c2 := rippleAdd (mkAdd_XY_S X Y Out h)
  let c3 := rippleSub (mkSub_SM_D1 r L)
  let q1 := evalRevList c1 q
  let q2 := evalRevList c2 q1
  let q3 := evalRevList c3 q2
  have hpre_eq : evalRevList (addModMPre M X Y Out h) q = q3 := by
    simp [addModMPre, evalRevList_append, c1, c2, c3, q1, q2, q3]
  have h1 := initNat_spec M (L + 1) (regM_w r L) (fun _ hi _ hj => regM_inj hi hj) q
  have hM_val : regVal q1 (regM_w r L) (L + 1) = M := by
    apply regVal_eq_of_testBit (by omega)
    intro j hj
    rw [show q1 (regM_w r L j) = evalRevList (initNat M (L + 1) (regM_w r L)) q (regM_w r L j) from rfl,
      h1.2 j hj, hq_scr _ regM_inScratch, Bool.false_xor]
  have hS_zero : ∀ t < L + 1, q1 (regS_w r L t) = false := fun t _ => by
    rw [show q1 (regS_w r L t) = evalRevList (initNat M (L + 1) (regM_w r L)) q (regS_w r L t) from rfl,
      h1.1 (regS_w r L t) (fun _ _ => regM_ne_regS.symm)]
    exact hq_scr _ regS_inScratch
  have hC_zero : ∀ t ≤ L + 1, q1 (regC_w r L t) = false := fun t _ => by
    rw [show q1 (regC_w r L t) = evalRevList (initNat M (L + 1) (regM_w r L)) q (regC_w r L t) from rfl,
      h1.1 (regC_w r L t) (fun _ _ => regM_ne_regC.symm)]
    exact hq_scr _ regC_inScratch
  have h2 := rippleAdd_spec (mkAdd_XY_S X Y Out h) q1 hS_zero hC_zero
  have hX1 : regVal q1 X (L + 1) = regVal q X (L + 1) := by
    apply regVal_eq_of_eq; intro j hj
    exact h1.1 (X j) (fun _ _ heq => h.X_ns j (by omega) (heq ▸ regM_inScratch))
  have hY1 : regVal q1 Y (L + 1) = regVal q Y (L + 1) := by
    apply regVal_eq_of_eq; intro j hj
    exact h1.1 (Y j) (fun _ _ heq => h.Y_ns j (by omega) (heq ▸ regM_inScratch))
  have hS_lt : regVal q X (L + 1) + regVal q Y (L + 1) < 2 ^ (L + 1) := by
    rw [pow_succ]; omega
  have hS_val : regVal q2 (regS_w r L) (L + 1) = regVal q X (L + 1) + regVal q Y (L + 1) := by
    have h2a := h2.2
    change regVal q2 (regS_w r L) (L + 1) + (q2 (regC_w r L (L + 1))).toNat * 2 ^ (L + 1) =
        regVal q1 X (L + 1) + regVal q1 Y (L + 1) at h2a
    rw [hX1, hY1] at h2a
    cases hc : q2 (regC_w r L (L + 1)) <;> simp [hc] at h2a <;> omega
  have hM2 : regVal q2 (regM_w r L) (L + 1) = M := by
    rw [← hM_val]
    apply regVal_eq_of_eq; intro j hj
    exact h2.1 (regM_w r L j) (fun _ _ => regM_ne_regS) (fun _ _ _ => regM_ne_regC)
  have hD1_zero : ∀ t < L + 1, q2 (regD1_w r L t) = false := fun t _ => by
    rw [show q2 (regD1_w r L t) = evalRevList c2 q1 (regD1_w r L t) from rfl,
      h2.1 (regD1_w r L t) (fun _ _ => regS_ne_regD1.symm) (fun _ _ _ => regC_ne_regD1.symm),
      show q1 (regD1_w r L t) = evalRevList c1 q (regD1_w r L t) from rfl,
      h1.1 (regD1_w r L t) (fun _ _ => regM_ne_regD1.symm)]
    exact hq_scr _ regD1_inScratch
  have hBr1_zero : ∀ t ≤ L + 1, q2 (regBr1_w r L t) = false := fun t _ => by
    rw [show q2 (regBr1_w r L t) = evalRevList c2 q1 (regBr1_w r L t) from rfl,
      h2.1 (regBr1_w r L t) (fun _ _ => regS_ne_regBr1.symm) (fun _ _ _ => regC_ne_regBr1.symm),
      show q1 (regBr1_w r L t) = evalRevList c1 q (regBr1_w r L t) from rfl,
      h1.1 (regBr1_w r L t) (fun _ _ => regM_ne_regBr1.symm)]
    exact hq_scr _ regBr1_inScratch
  have h3 := rippleSub_spec (mkSub_SM_D1 r L) q2 hD1_zero hBr1_zero
  have hS3 : regVal q3 (regS_w r L) (L + 1) = regVal q X (L + 1) + regVal q Y (L + 1) := by
    rw [← hS_val]
    apply regVal_eq_of_eq; intro j hj
    exact h3.1 (regS_w r L j) (fun _ _ => regS_ne_regD1) (fun _ _ _ => regS_ne_regBr1)
  have hBr_lt : q3 (regBr1_w r L (L + 1)) =
      decide (regVal q X (L + 1) + regVal q Y (L + 1) < M) := by
    have h3b := h3.2.1
    change q3 (regBr1_w r L (L + 1)) =
      decide (regVal q2 (regS_w r L) (L + 1) < regVal q2 (regM_w r L) (L + 1)) at h3b
    rwa [hS_val, hM2] at h3b
  have hD1_diff : M ≤ regVal q X (L + 1) + regVal q Y (L + 1) →
      regVal q3 (regD1_w r L) (L + 1) = regVal q X (L + 1) + regVal q Y (L + 1) - M := by
    intro hle
    have h3d := h3.2.2
    change regVal q2 (regM_w r L) (L + 1) ≤ regVal q2 (regS_w r L) (L + 1) →
        regVal q3 (regD1_w r L) (L + 1) =
          regVal q2 (regS_w r L) (L + 1) - regVal q2 (regM_w r L) (L + 1) at h3d
    rw [hS_val, hM2] at h3d
    exact h3d hle
  have hOut_inj : ∀ i < L, ∀ j < L, Out i = Out j → i = j := h.Out_inj
  have hq3_out : ∀ j < L, q3 (Out j) = false := fun j hj => by
    have h3o : q3 (Out j) = q2 (Out j) :=
      h3.1 (Out j) (fun _ _ heq => h.Out_ns j hj (heq ▸ regD1_inScratch))
        (fun _ _ _ heq => h.Out_ns j hj (heq ▸ regBr1_inScratch))
    have h2o : q2 (Out j) = q1 (Out j) :=
      h2.1 (Out j) (fun _ _ heq => h.Out_ns j hj (heq ▸ regS_inScratch))
        (fun _ _ _ heq => h.Out_ns j hj (heq ▸ regC_inScratch))
    have h1o : q1 (Out j) = q (Out j) :=
      h1.1 (Out j) (fun _ _ heq => h.Out_ns j hj (heq ▸ regM_inScratch))
    rw [h3o, h2o, h1o, hq_out j hj]
  let cCopy1 := ccxLoop (regBr1_w r L (L + 1)) (regS_w r L) Out L
      (fun _ _ => regBr1_ne_regS)
      (fun j hj heq => h.Out_ns j hj (heq ▸ regBr1_inScratch))
      (fun j hj heq => h.Out_ns j hj (heq ▸ regS_inScratch))
  let cCopy2 := ccxLoop (regBr1_w r L (L + 1)) (regD1_w r L) Out L
      (fun _ _ => regBr1_ne_regD1)
      (fun j hj heq => h.Out_ns j hj (heq ▸ regBr1_inScratch))
      (fun j hj heq => h.Out_ns j hj (heq ▸ regD1_inScratch))
  have hc1_spec := ccxLoop_spec (regBr1_w r L (L + 1)) (regS_w r L) Out L
    (fun _ _ => regBr1_ne_regS)
    (fun j hj heq => h.Out_ns j hj (heq ▸ regBr1_inScratch))
    (fun _ _ j hj heq => h.Out_ns j hj (heq ▸ regS_inScratch)) hOut_inj q3
  let q4 := evalRevList cCopy1 q3
  let q5 := evalRev (.x (regBr1_w r L (L + 1))) q4
  have hc2_spec := ccxLoop_spec (regBr1_w r L (L + 1)) (regD1_w r L) Out L
    (fun _ _ => regBr1_ne_regD1)
    (fun j hj heq => h.Out_ns j hj (heq ▸ regBr1_inScratch))
    (fun _ _ j hj heq => h.Out_ns j hj (heq ▸ regD1_inScratch)) hOut_inj q5
  let q6 := evalRevList cCopy2 q5
  let q7 := evalRev (.x (regBr1_w r L (L + 1))) q6
  have hcopy_eq : evalRevList (addModMCopy X Y Out h) q3 = q7 := by
    simp [addModMCopy, evalRevList_append, cCopy1, cCopy2, q4, q5, q6, q7]
  have hq7_non_out : ∀ z, (∀ j < L, z ≠ Out j) → q7 z = q3 z := by
    intro z hz
    have h4z : q4 z = q3 z := hc1_spec.1 z hz
    have h6z : q6 z = q5 z := hc2_spec.1 z hz
    by_cases hzb : z = regBr1_w r L (L + 1)
    · rw [hzb]
      have h6b : q6 (regBr1_w r L (L + 1)) = q5 (regBr1_w r L (L + 1)) := hzb ▸ h6z
      have h4b : q4 (regBr1_w r L (L + 1)) = q3 (regBr1_w r L (L + 1)) := hzb ▸ h4z
      dsimp only [q7]
      rw [evalRev_x, Function.update_self, h6b]
      dsimp only [q5]
      rw [evalRev_x, Function.update_self, h4b, Bool.not_not]
    · dsimp only [q7]
      rw [evalRev_x, Function.update_of_ne hzb, h6z]
      dsimp only [q5]
      rw [evalRev_x, Function.update_of_ne hzb, h4z]
  have hq7_out : ∀ j < L, q7 (Out j) =
      ((regVal q X (L + 1) + regVal q Y (L + 1)) % M).testBit j := by
    intro j hj
    have hneBr : Out j ≠ regBr1_w r L (L + 1) :=
      fun heq => h.Out_ns j hj (heq ▸ regBr1_inScratch)
    have hq7j : q7 (Out j) = q6 (Out j) := by simp [q7, hneBr]
    have hq5Br : q5 (regBr1_w r L (L + 1)) = !(q3 (regBr1_w r L (L + 1))) := by
      have h4Br : q4 (regBr1_w r L (L + 1)) = q3 (regBr1_w r L (L + 1)) :=
        hc1_spec.1 _ (fun t ht heq => h.Out_ns t ht (heq ▸ regBr1_inScratch))
      simp [q5, h4Br]
    have hq5D1 : q5 (regD1_w r L j) = q3 (regD1_w r L j) := by
      have h4D : q4 (regD1_w r L j) = q3 (regD1_w r L j) :=
        hc1_spec.1 _ (fun t ht heq => h.Out_ns t ht (heq ▸ regD1_inScratch))
      have hneD : regD1_w r L j ≠ regBr1_w r L (L + 1) := regD1_ne_regBr1
      simp [q5, hneD, h4D]
    have hq5Out : q5 (Out j) = q4 (Out j) := by simp [q5, hneBr]
    have hq6Out : q6 (Out j) = evalRevList cCopy2 q5 (Out j) := rfl
    have hq4Out : q4 (Out j) = evalRevList cCopy1 q3 (Out j) := rfl
    rw [hq7j, hq6Out, hc2_spec.2 j hj, hq5Out, hq4Out, hc1_spec.2 j hj, hq3_out j hj,
      Bool.false_xor, hq5Br, hq5D1, hBr_lt]
    by_cases hlt : regVal q X (L + 1) + regVal q Y (L + 1) < M
    · have hmod : (regVal q X (L + 1) + regVal q Y (L + 1)) % M =
          regVal q X (L + 1) + regVal q Y (L + 1) := Nat.mod_eq_of_lt hlt
      rw [hmod, decide_eq_true hlt]
      simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.xor_false]
      rw [← regVal_testBit q3 (regS_w r L) (k := L + 1) (by omega), hS3]
    · have hle : M ≤ regVal q X (L + 1) + regVal q Y (L + 1) := by omega
      have hsub_lt : regVal q X (L + 1) + regVal q Y (L + 1) - M < M := by omega
      have hmod : (regVal q X (L + 1) + regVal q Y (L + 1)) % M =
          regVal q X (L + 1) + regVal q Y (L + 1) - M := by
        rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hsub_lt]
      rw [hmod, decide_eq_false hlt]
      simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_xor]
      rw [← regVal_testBit q3 (regD1_w r L) (k := L + 1) (by omega), hD1_diff hle]
  let P_out : Fin (fbOutW_raw r L) → Prop := fun z => ∃ j < L, z = Out j
  have hPre_av : ∀ g ∈ (addModMPre M X Y Out h).reverse, gateAvoids P_out g := by
    intro g hg
    rw [List.mem_reverse] at hg
    apply addModMPre_avoid_Out M X Y Out h P_out
    · rintro i hi ⟨j, hj, heq⟩; exact h.XOut i hi j hj heq
    · rintro i hi ⟨j, hj, heq⟩; exact h.YOut i hi j hj heq
    · rintro z hz ⟨j, hj, heq⟩; exact h.Out_ns j hj (by rw [← heq]; exact hz)
    · exact hg
  have hcomm := evalRevList_update_comm P_out (addModMPre M X Y Out h).reverse hPre_av q3 q7
    (fun z hz => (hq7_non_out z (fun j hj heq => hz ⟨j, hj, heq⟩)).symm)
  have hrev : evalRevList (addModMPre M X Y Out h).reverse q3 = q := by
    rw [← hpre_eq]
    exact evalRevList_reverse _ q
  have hq'_eq : q' = evalRevList (addModMPre M X Y Out h).reverse q7 := by
    simp [q', addModM, evalRevList_append, hpre_eq, hcopy_eq]
  rw [hq'_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hzP : ¬ P_out z := fun ⟨j, hj, heq⟩ => hz j hj heq
    rw [← hcomm.1 z hzP, hrev]
  · intro z hz
    have hzP : ¬ P_out z := fun ⟨j, hj, heq⟩ => h.Out_ns j hj (by rw [← heq]; exact hz)
    rw [← hcomm.1 z hzP, hrev, hq_scr z hz]
  · intro j hj
    have hjP : P_out (Out j) := ⟨j, hj, rfl⟩
    rw [hcomm.2 (Out j) hjP, hq7_out j hj]

def subModMPre {r L : ℕ} (M : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) : List (RevGate (fbOutW_raw r L)) :=
  initNat M (L + 1) (regM_w r L) ++
    rippleAdd (mkAdd_XM_S X Y Out h) ++
    rippleSub (mkSub_XY_D1 X Y Out h) ++
    rippleSub (mkSub_SY_D2 X Y Out h)

def subModMCopy {r L : ℕ} (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) : List (RevGate (fbOutW_raw r L)) :=
  ccxLoop (regBr1_w r L (L + 1)) (regD2_w r L) Out L
      (fun j _ heq => by simp only [regBr1_w, regD2_w, Fin.ext_iff] at heq; omega)
      (fun j hj heq => h.Out_ns j hj (by rw [← heq]; exact regBr1_inScratch))
      (fun j hj heq => h.Out_ns j hj (by rw [← heq]; exact regD2_inScratch)) ++
    [.x (regBr1_w r L (L + 1))] ++
    ccxLoop (regBr1_w r L (L + 1)) (regD1_w r L) Out L
      (fun j _ heq => by simp only [regBr1_w, regD1_w, Fin.ext_iff] at heq; omega)
      (fun j hj heq => h.Out_ns j hj (by rw [← heq]; exact regBr1_inScratch))
      (fun j hj heq => h.Out_ns j hj (by rw [← heq]; exact regD1_inScratch)) ++
    [.x (regBr1_w r L (L + 1))]

def subModM {r L : ℕ} (M : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) : List (RevGate (fbOutW_raw r L)) :=
  subModMPre M X Y Out h ++ subModMCopy X Y Out h ++ (subModMPre M X Y Out h).reverse

lemma subModM_length {r L : ℕ} (M : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) :
    (subModM M X Y Out h).length ≤ 42 * L + 42 := by
  have hpre : (subModMPre M X Y Out h).length ≤ 20 * L + 20 := by
    simp only [subModMPre, List.length_append, rippleAdd_length, rippleSub_length]
    have hi := initNat_length M (L + 1) (regM_w r L)
    omega
  have hcopy : (subModMCopy X Y Out h).length = 2 * L + 2 := by
    simp [subModMCopy, ccxLoop_length]; omega
  simp only [subModM, List.length_append, List.length_reverse]
  omega

lemma subModMPre_avoid_Out {r L : ℕ} (M : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) (P : Fin (fbOutW_raw r L) → Prop)
    (hPX : ∀ i ≤ L, ¬ P (X i)) (hPY : ∀ i ≤ L, ¬ P (Y i))
    (hPS : ∀ z, InScratch r L z → ¬ P z) :
    ∀ g ∈ subModMPre M X Y Out h, gateAvoids P g := by
  have hM : ∀ j < L + 1, ¬ P (regM_w r L j) := fun _ _ => hPS _ regM_inScratch
  have hS : ∀ j < L + 1, ¬ P (regS_w r L j) := fun _ _ => hPS _ regS_inScratch
  have hC : ∀ j ≤ L + 1, ¬ P (regC_w r L j) := fun _ _ => hPS _ regC_inScratch
  have hD1 : ∀ j < L + 1, ¬ P (regD1_w r L j) := fun _ _ => hPS _ regD1_inScratch
  have hBr1 : ∀ j ≤ L + 1, ¬ P (regBr1_w r L j) := fun _ _ => hPS _ regBr1_inScratch
  have hD2 : ∀ j < L + 1, ¬ P (regD2_w r L j) := fun _ _ => hPS _ regD2_inScratch
  have hBr2 : ∀ j ≤ L + 1, ¬ P (regBr2_w r L j) := fun _ _ => hPS _ regBr2_inScratch
  intro g hg
  simp only [subModMPre, List.mem_append] at hg
  rcases hg with ((hg | hg) | hg) | hg
  · exact initNat_avoid P M (L + 1) (regM_w r L) hM g hg
  · exact rippleAdd_avoid (mkAdd_XM_S X Y Out h) P (fun j hj => hPX j (by omega)) hM hS hC g hg
  · exact rippleSub_avoid (mkSub_XY_D1 X Y Out h) P (fun j hj => hPX j (by omega))
      (fun j hj => hPY j (by omega)) hD1 hBr1 g hg
  · exact rippleSub_avoid (mkSub_SY_D2 X Y Out h) P hS (fun j hj => hPY j (by omega)) hD2 hBr2 g hg

lemma subModM_avoid {r L : ℕ} (M : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (h : ValidModIO r L X Y Out) (P : Fin (fbOutW_raw r L) → Prop)
    (hPX : ∀ i ≤ L, ¬ P (X i)) (hPY : ∀ i ≤ L, ¬ P (Y i))
    (hPOut : ∀ j < L, ¬ P (Out j)) (hPS : ∀ z, InScratch r L z → ¬ P z) :
    ∀ g ∈ subModM M X Y Out h, gateAvoids P g := by
  have hpre : ∀ g ∈ subModMPre M X Y Out h, gateAvoids P g :=
    subModMPre_avoid_Out M X Y Out h P hPX hPY hPS
  have hcopy : ∀ g ∈ subModMCopy X Y Out h, gateAvoids P g := by
    intro g hg
    simp only [subModMCopy, List.mem_append, List.mem_singleton] at hg
    rcases hg with ((hg | rfl) | hg) | rfl
    · exact ccxLoop_avoid P _ _ _ L _ _ _ (hPS _ regBr1_inScratch)
        (fun _ _ => hPS _ regD2_inScratch) hPOut g hg
    · exact hPS _ regBr1_inScratch
    · exact ccxLoop_avoid P _ _ _ L _ _ _ (hPS _ regBr1_inScratch)
        (fun _ _ => hPS _ regD1_inScratch) hPOut g hg
    · exact hPS _ regBr1_inScratch
  intro g hg
  simp only [subModM, List.mem_append, List.mem_reverse] at hg
  rcases hg with (hg | hg) | hg
  · exact hpre g hg
  · exact hcopy g hg
  · exact hpre g hg

lemma subModM_spec {r L : ℕ} (M : ℕ) (_ : 1 ≤ M) (hML : M < 2 ^ L)
    (X Y Out : ℕ → Fin (fbOutW_raw r L)) (h : ValidModIO r L X Y Out)
    (q : Qubits (fbOutW_raw r L))
    (hq_scr : ∀ z, InScratch r L z → q z = false)
    (hq_out : ∀ j < L, q (Out j) = false)
    (hqX : regVal q X (L + 1) < M) (hqY : regVal q Y (L + 1) < M) :
    let q' := evalRevList (subModM M X Y Out h) q
    (∀ z, (∀ j < L, z ≠ Out j) → q' z = q z) ∧
      (∀ z, InScratch r L z → q' z = false) ∧
      (∀ j < L, q' (Out j) = ((M + regVal q X (L + 1) - regVal q Y (L + 1)) % M).testBit j) := by
  intro q'
  let c1 := initNat M (L + 1) (regM_w r L)
  let c2 := rippleAdd (mkAdd_XM_S X Y Out h)
  let c3 := rippleSub (mkSub_XY_D1 X Y Out h)
  let c4 := rippleSub (mkSub_SY_D2 X Y Out h)
  let q1 := evalRevList c1 q
  let q2 := evalRevList c2 q1
  let q3 := evalRevList c3 q2
  let q4 := evalRevList c4 q3
  have hpre_eq : evalRevList (subModMPre M X Y Out h) q = q4 := by
    simp [subModMPre, evalRevList_append, c1, c2, c3, c4, q1, q2, q3, q4]
  have h1 := initNat_spec M (L + 1) (regM_w r L) (fun _ hi _ hj => regM_inj hi hj) q
  have hM_val : regVal q1 (regM_w r L) (L + 1) = M := by
    apply regVal_eq_of_testBit (by omega)
    intro j hj
    rw [show q1 (regM_w r L j) = evalRevList c1 q (regM_w r L j) from rfl,
      h1.2 j hj, hq_scr _ regM_inScratch, Bool.false_xor]
  have hS_zero : ∀ t < L + 1, q1 (regS_w r L t) = false := fun t _ => by
    rw [show q1 (regS_w r L t) = evalRevList c1 q (regS_w r L t) from rfl,
      h1.1 (regS_w r L t) (fun _ _ => regM_ne_regS.symm)]
    exact hq_scr _ regS_inScratch
  have hC_zero : ∀ t ≤ L + 1, q1 (regC_w r L t) = false := fun t _ => by
    rw [show q1 (regC_w r L t) = evalRevList c1 q (regC_w r L t) from rfl,
      h1.1 (regC_w r L t) (fun _ _ => regM_ne_regC.symm)]
    exact hq_scr _ regC_inScratch
  have h2 := rippleAdd_spec (mkAdd_XM_S X Y Out h) q1 hS_zero hC_zero
  have hX1 : regVal q1 X (L + 1) = regVal q X (L + 1) := by
    apply regVal_eq_of_eq; intro j hj
    exact h1.1 (X j) (fun _ _ heq => h.X_ns j (by omega) (heq ▸ regM_inScratch))
  have hS_val : regVal q2 (regS_w r L) (L + 1) = regVal q X (L + 1) + M := by
    have h2a := h2.2
    change regVal q2 (regS_w r L) (L + 1) + (q2 (regC_w r L (L + 1))).toNat * 2 ^ (L + 1) =
        regVal q1 X (L + 1) + regVal q1 (regM_w r L) (L + 1) at h2a
    rw [hX1, hM_val] at h2a
    have hlt : regVal q X (L + 1) + M < 2 ^ (L + 1) := by rw [pow_succ]; omega
    cases hc : q2 (regC_w r L (L + 1)) <;> simp [hc] at h2a <;> omega
  have hX2 : regVal q2 X (L + 1) = regVal q X (L + 1) := by
    rw [← hX1]
    apply regVal_eq_of_eq; intro j hj
    exact h2.1 (X j) (fun _ _ heq => h.X_ns j (by omega) (heq ▸ regS_inScratch))
      (fun _ _ _ heq => h.X_ns j (by omega) (heq ▸ regC_inScratch))
  have hY2 : regVal q2 Y (L + 1) = regVal q Y (L + 1) := by
    apply regVal_eq_of_eq; intro j hj
    have h2y := h2.1 (Y j) (fun _ _ heq => h.Y_ns j (by omega) (heq ▸ regS_inScratch))
      (fun _ _ _ heq => h.Y_ns j (by omega) (heq ▸ regC_inScratch))
    have h1y := h1.1 (Y j) (fun _ _ heq => h.Y_ns j (by omega) (heq ▸ regM_inScratch))
    exact h2y.trans h1y
  have hD1_zero : ∀ t < L + 1, q2 (regD1_w r L t) = false := fun t _ => by
    rw [show q2 (regD1_w r L t) = evalRevList c2 q1 (regD1_w r L t) from rfl,
      h2.1 (regD1_w r L t) (fun _ _ => regS_ne_regD1.symm) (fun _ _ _ => regC_ne_regD1.symm),
      show q1 (regD1_w r L t) = evalRevList c1 q (regD1_w r L t) from rfl,
      h1.1 (regD1_w r L t) (fun _ _ => regM_ne_regD1.symm)]
    exact hq_scr _ regD1_inScratch
  have hBr1_zero : ∀ t ≤ L + 1, q2 (regBr1_w r L t) = false := fun t _ => by
    rw [show q2 (regBr1_w r L t) = evalRevList c2 q1 (regBr1_w r L t) from rfl,
      h2.1 (regBr1_w r L t) (fun _ _ => regS_ne_regBr1.symm) (fun _ _ _ => regC_ne_regBr1.symm),
      show q1 (regBr1_w r L t) = evalRevList c1 q (regBr1_w r L t) from rfl,
      h1.1 (regBr1_w r L t) (fun _ _ => regM_ne_regBr1.symm)]
    exact hq_scr _ regBr1_inScratch
  have h3 := rippleSub_spec (mkSub_XY_D1 X Y Out h) q2 hD1_zero hBr1_zero
  have hS3 : regVal q3 (regS_w r L) (L + 1) = regVal q X (L + 1) + M := by
    rw [← hS_val]
    apply regVal_eq_of_eq; intro j hj
    exact h3.1 (regS_w r L j) (fun _ _ => regS_ne_regD1) (fun _ _ _ => regS_ne_regBr1)
  have hY3 : regVal q3 Y (L + 1) = regVal q Y (L + 1) := by
    rw [← hY2]
    apply regVal_eq_of_eq; intro j hj
    exact h3.1 (Y j) (fun _ _ heq => h.Y_ns j (by omega) (heq ▸ regD1_inScratch))
      (fun _ _ _ heq => h.Y_ns j (by omega) (heq ▸ regBr1_inScratch))
  have hD2_zero : ∀ t < L + 1, q3 (regD2_w r L t) = false := fun t _ => by
    rw [show q3 (regD2_w r L t) = evalRevList c3 q2 (regD2_w r L t) from rfl,
      h3.1 (regD2_w r L t) (fun _ _ => regD1_ne_regD2.symm) (fun _ _ _ => regBr1_ne_regD2.symm),
      show q2 (regD2_w r L t) = evalRevList c2 q1 (regD2_w r L t) from rfl,
      h2.1 (regD2_w r L t) (fun _ _ => regS_ne_regD2.symm) (fun _ _ _ => regC_ne_regD2.symm),
      show q1 (regD2_w r L t) = evalRevList c1 q (regD2_w r L t) from rfl,
      h1.1 (regD2_w r L t) (fun _ _ => regM_ne_regD2.symm)]
    exact hq_scr _ regD2_inScratch
  have hBr2_zero : ∀ t ≤ L + 1, q3 (regBr2_w r L t) = false := fun t _ => by
    rw [show q3 (regBr2_w r L t) = evalRevList c3 q2 (regBr2_w r L t) from rfl,
      h3.1 (regBr2_w r L t) (fun _ _ => regD1_ne_regBr2.symm) (fun _ _ _ => regBr1_ne_regBr2.symm),
      show q2 (regBr2_w r L t) = evalRevList c2 q1 (regBr2_w r L t) from rfl,
      h2.1 (regBr2_w r L t) (fun _ _ => regS_ne_regBr2.symm) (fun _ _ _ => regC_ne_regBr2.symm),
      show q1 (regBr2_w r L t) = evalRevList c1 q (regBr2_w r L t) from rfl,
      h1.1 (regBr2_w r L t) (fun _ _ => regM_ne_regBr2.symm)]
    exact hq_scr _ regBr2_inScratch
  have h4 := rippleSub_spec (mkSub_SY_D2 X Y Out h) q3 hD2_zero hBr2_zero
  have hBr1_val : q4 (regBr1_w r L (L + 1)) = decide (regVal q X (L + 1) < regVal q Y (L + 1)) := by
    have h4b : q4 (regBr1_w r L (L + 1)) = q3 (regBr1_w r L (L + 1)) :=
      h4.1 _ (fun _ _ => regBr1_ne_regD2) (fun _ _ _ => regBr1_ne_regBr2)
    rw [h4b]
    have h3b := h3.2.1
    change q3 (regBr1_w r L (L + 1)) = decide (regVal q2 X (L + 1) < regVal q2 Y (L + 1)) at h3b
    rwa [hX2, hY2] at h3b
  have hD1_diff : regVal q Y (L + 1) ≤ regVal q X (L + 1) →
      regVal q4 (regD1_w r L) (L + 1) = regVal q X (L + 1) - regVal q Y (L + 1) := by
    intro hle
    have hD1_eq : regVal q4 (regD1_w r L) (L + 1) = regVal q3 (regD1_w r L) (L + 1) := by
      apply regVal_eq_of_eq; intro j hj
      exact h4.1 _ (fun _ _ => regD1_ne_regD2) (fun _ _ _ => regD1_ne_regBr2)
    rw [hD1_eq]
    have h3d := h3.2.2
    change regVal q2 Y (L + 1) ≤ regVal q2 X (L + 1) →
        regVal q3 (regD1_w r L) (L + 1) = regVal q2 X (L + 1) - regVal q2 Y (L + 1) at h3d
    rw [hX2, hY2] at h3d
    exact h3d hle
  have hD2_diff : regVal q4 (regD2_w r L) (L + 1) = regVal q X (L + 1) + M - regVal q Y (L + 1) := by
    have h4d := h4.2.2
    change regVal q3 Y (L + 1) ≤ regVal q3 (regS_w r L) (L + 1) →
        regVal q4 (regD2_w r L) (L + 1) =
          regVal q3 (regS_w r L) (L + 1) - regVal q3 Y (L + 1) at h4d
    rw [hS3, hY3] at h4d
    exact h4d (by omega)
  have hq4_out : ∀ j < L, q4 (Out j) = false := fun j hj => by
    have h4o : q4 (Out j) = q3 (Out j) :=
      h4.1 _ (fun _ _ heq => h.Out_ns j hj (heq ▸ regD2_inScratch))
        (fun _ _ _ heq => h.Out_ns j hj (heq ▸ regBr2_inScratch))
    have h3o : q3 (Out j) = q2 (Out j) :=
      h3.1 _ (fun _ _ heq => h.Out_ns j hj (heq ▸ regD1_inScratch))
        (fun _ _ _ heq => h.Out_ns j hj (heq ▸ regBr1_inScratch))
    have h2o : q2 (Out j) = q1 (Out j) :=
      h2.1 _ (fun _ _ heq => h.Out_ns j hj (heq ▸ regS_inScratch))
        (fun _ _ _ heq => h.Out_ns j hj (heq ▸ regC_inScratch))
    have h1o : q1 (Out j) = q (Out j) :=
      h1.1 _ (fun _ _ heq => h.Out_ns j hj (heq ▸ regM_inScratch))
    rw [h4o, h3o, h2o, h1o, hq_out j hj]
  let cCopy1 := ccxLoop (regBr1_w r L (L + 1)) (regD2_w r L) Out L
      (fun _ _ => regBr1_ne_regD2)
      (fun j hj heq => h.Out_ns j hj (heq ▸ regBr1_inScratch))
      (fun j hj heq => h.Out_ns j hj (heq ▸ regD2_inScratch))
  let cCopy2 := ccxLoop (regBr1_w r L (L + 1)) (regD1_w r L) Out L
      (fun _ _ => regBr1_ne_regD1)
      (fun j hj heq => h.Out_ns j hj (heq ▸ regBr1_inScratch))
      (fun j hj heq => h.Out_ns j hj (heq ▸ regD1_inScratch))
  have hc1_spec := ccxLoop_spec (regBr1_w r L (L + 1)) (regD2_w r L) Out L
    (fun _ _ => regBr1_ne_regD2)
    (fun j hj heq => h.Out_ns j hj (heq ▸ regBr1_inScratch))
    (fun _ _ j hj heq => h.Out_ns j hj (heq ▸ regD2_inScratch)) h.Out_inj q4
  let q5 := evalRevList cCopy1 q4
  let q6 := evalRev (.x (regBr1_w r L (L + 1))) q5
  have hc2_spec := ccxLoop_spec (regBr1_w r L (L + 1)) (regD1_w r L) Out L
    (fun _ _ => regBr1_ne_regD1)
    (fun j hj heq => h.Out_ns j hj (heq ▸ regBr1_inScratch))
    (fun _ _ j hj heq => h.Out_ns j hj (heq ▸ regD1_inScratch)) h.Out_inj q6
  let q7 := evalRevList cCopy2 q6
  let q8 := evalRev (.x (regBr1_w r L (L + 1))) q7
  have hcopy_eq : evalRevList (subModMCopy X Y Out h) q4 = q8 := by
    simp [subModMCopy, evalRevList_append, cCopy1, cCopy2, q5, q6, q7, q8]
  have hq8_non_out : ∀ z, (∀ j < L, z ≠ Out j) → q8 z = q4 z := by
    intro z hz
    have h5z : q5 z = q4 z := hc1_spec.1 z hz
    have h7z : q7 z = q6 z := hc2_spec.1 z hz
    by_cases hzb : z = regBr1_w r L (L + 1)
    · rw [hzb]
      have h7b : q7 (regBr1_w r L (L + 1)) = q6 (regBr1_w r L (L + 1)) := hzb ▸ h7z
      have h5b : q5 (regBr1_w r L (L + 1)) = q4 (regBr1_w r L (L + 1)) := hzb ▸ h5z
      dsimp only [q8]
      rw [evalRev_x, Function.update_self, h7b]
      dsimp only [q6]
      rw [evalRev_x, Function.update_self, h5b, Bool.not_not]
    · dsimp only [q8]
      rw [evalRev_x, Function.update_of_ne hzb, h7z]
      dsimp only [q6]
      rw [evalRev_x, Function.update_of_ne hzb, h5z]
  have hq8_out : ∀ j < L, q8 (Out j) =
      ((M + regVal q X (L + 1) - regVal q Y (L + 1)) % M).testBit j := by
    intro j hj
    have hneBr : Out j ≠ regBr1_w r L (L + 1) :=
      fun heq => h.Out_ns j hj (heq ▸ regBr1_inScratch)
    have hq8j : q8 (Out j) = q7 (Out j) := by simp [q8, hneBr]
    have hq6Br : q6 (regBr1_w r L (L + 1)) = !(q4 (regBr1_w r L (L + 1))) := by
      have h5Br : q5 (regBr1_w r L (L + 1)) = q4 (regBr1_w r L (L + 1)) :=
        hc1_spec.1 _ (fun t ht heq => h.Out_ns t ht (heq ▸ regBr1_inScratch))
      simp [q6, h5Br]
    have hq6D1 : q6 (regD1_w r L j) = q4 (regD1_w r L j) := by
      have h5D : q5 (regD1_w r L j) = q4 (regD1_w r L j) :=
        hc1_spec.1 _ (fun t ht heq => h.Out_ns t ht (heq ▸ regD1_inScratch))
      have hneD : regD1_w r L j ≠ regBr1_w r L (L + 1) := regD1_ne_regBr1
      simp [q6, hneD, h5D]
    have hq6Out : q6 (Out j) = q5 (Out j) := by simp [q6, hneBr]
    have hq7Out : q7 (Out j) = evalRevList cCopy2 q6 (Out j) := rfl
    have hq5Out : q5 (Out j) = evalRevList cCopy1 q4 (Out j) := rfl
    rw [hq8j, hq7Out, hc2_spec.2 j hj, hq6Out, hq5Out, hc1_spec.2 j hj, hq4_out j hj,
      Bool.false_xor, hq6Br, hq6D1, hBr1_val]
    by_cases hlt : regVal q X (L + 1) < regVal q Y (L + 1)
    · have hsub_lt : M + regVal q X (L + 1) - regVal q Y (L + 1) < M := by omega
      have hmod : (M + regVal q X (L + 1) - regVal q Y (L + 1)) % M =
          regVal q X (L + 1) + M - regVal q Y (L + 1) := by
        rw [show M + regVal q X (L + 1) - regVal q Y (L + 1) =
            regVal q X (L + 1) + M - regVal q Y (L + 1) by omega,
          Nat.mod_eq_of_lt (by omega)]
      rw [hmod, decide_eq_true hlt]
      simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.xor_false]
      rw [← regVal_testBit q4 (regD2_w r L) (k := L + 1) (by omega), hD2_diff]
    · have hle : regVal q Y (L + 1) ≤ regVal q X (L + 1) := by omega
      have hsub_lt : regVal q X (L + 1) - regVal q Y (L + 1) < M := by omega
      have hmod : (M + regVal q X (L + 1) - regVal q Y (L + 1)) % M =
          regVal q X (L + 1) - regVal q Y (L + 1) := by
        rw [show M + regVal q X (L + 1) - regVal q Y (L + 1) =
            (regVal q X (L + 1) - regVal q Y (L + 1)) + M by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hsub_lt]
      rw [hmod, decide_eq_false hlt]
      simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_xor]
      rw [← regVal_testBit q4 (regD1_w r L) (k := L + 1) (by omega), hD1_diff hle]
  let P_out : Fin (fbOutW_raw r L) → Prop := fun z => ∃ j < L, z = Out j
  have hPre_av : ∀ g ∈ (subModMPre M X Y Out h).reverse, gateAvoids P_out g := by
    intro g hg
    rw [List.mem_reverse] at hg
    apply subModMPre_avoid_Out M X Y Out h P_out
    · rintro i hi ⟨j, hj, heq⟩; exact h.XOut i hi j hj heq
    · rintro i hi ⟨j, hj, heq⟩; exact h.YOut i hi j hj heq
    · rintro z hz ⟨j, hj, heq⟩; exact h.Out_ns j hj (by rw [← heq]; exact hz)
    · exact hg
  have hcomm := evalRevList_update_comm P_out (subModMPre M X Y Out h).reverse hPre_av q4 q8
    (fun z hz => (hq8_non_out z (fun j hj heq => hz ⟨j, hj, heq⟩)).symm)
  have hrev : evalRevList (subModMPre M X Y Out h).reverse q4 = q := by
    rw [← hpre_eq]
    exact evalRevList_reverse _ q
  have hq'_eq : q' = evalRevList (subModMPre M X Y Out h).reverse q8 := by
    simp [q', subModM, evalRevList_append, hpre_eq, hcopy_eq]
  rw [hq'_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hzP : ¬ P_out z := fun ⟨j, hj, heq⟩ => hz j hj heq
    rw [← hcomm.1 z hzP, hrev]
  · intro z hz
    have hzP : ¬ P_out z := fun ⟨j, hj, heq⟩ => h.Out_ns j hj (by rw [← heq]; exact hz)
    rw [← hcomm.1 z hzP, hrev, hq_scr z hz]
  · intro j hj
    have hjP : P_out (Out j) := ⟨j, hj, rfl⟩
    rw [hcomm.2 (Out j) hjP, hq8_out j hj]

def liftReg (L : ℕ) {n : ℕ} (X : ℕ → Fin n) (z : Fin n) (j : ℕ) : Fin n :=
  if j < L then X j else z

lemma regVal_liftReg {n : ℕ} (L : ℕ) (X : ℕ → Fin n) (z : Fin n) (q : Qubits n)
    (hz : q z = false) :
    regVal q (liftReg L X z) (L + 1) = regVal q X L := by
  rw [regVal_succ]
  have hL : liftReg L X z L = z := by simp [liftReg]
  rw [hL, hz, Bool.toNat_false, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp [liftReg, Finset.mem_range.mp hj]

def fbOutCCU {n : ℕ} (L : ℕ) (pre : List (RevGate n)) (ctrl : Fin n) (src dst : ℕ → Fin n)
    (hcs : ∀ j < L, ctrl ≠ src j) (hcd : ∀ j < L, ctrl ≠ dst j)
    (hsd : ∀ j < L, src j ≠ dst j) : List (RevGate n) :=
  pre ++ ccxLoop ctrl src dst L hcs hcd hsd ++ pre.reverse

lemma fbOutCCU_length {n : ℕ} (L : ℕ) (pre : List (RevGate n)) (ctrl : Fin n)
    (src dst : ℕ → Fin n)
    (hcs : ∀ j < L, ctrl ≠ src j) (hcd : ∀ j < L, ctrl ≠ dst j)
    (hsd : ∀ j < L, src j ≠ dst j) :
    (fbOutCCU L pre ctrl src dst hcs hcd hsd).length = 2 * pre.length + L := by
  simp only [fbOutCCU, List.length_append, List.length_reverse, ccxLoop_length]
  omega

lemma fbOutCCU_spec {n : ℕ} (L : ℕ) (pre : List (RevGate n)) (ctrl : Fin n)
    (src dst : ℕ → Fin n)
    (hcs : ∀ j < L, ctrl ≠ src j) (hcd : ∀ j < L, ctrl ≠ dst j)
    (hsd : ∀ i < L, ∀ j < L, src i ≠ dst j)
    (hd_inj : ∀ i < L, ∀ j < L, dst i = dst j → i = j)
    (hPre_avoid : ∀ g ∈ pre, gateAvoids (fun z => ∃ j < L, z = dst j) g)
    (q : Qubits n)
    (hPre_ctrl : evalRevList pre q ctrl = q ctrl)
    (hPre_dst : ∀ j < L, evalRevList pre q (dst j) = q (dst j)) :
    let q1 := evalRevList pre q
    let q' := evalRevList (fbOutCCU L pre ctrl src dst hcs hcd (fun j hj => hsd j hj j hj)) q
    (∀ z, (∀ j < L, z ≠ dst j) → q' z = q z) ∧
      (∀ j < L, q' (dst j) = xor (q (dst j)) (q ctrl && q1 (src j))) := by
  intro q1 q'
  let P_dst : Fin n → Prop := fun z => ∃ j < L, z = dst j
  have hc := ccxLoop_spec ctrl src dst L hcs hcd hsd hd_inj q1
  let q2 := evalRevList (ccxLoop ctrl src dst L hcs hcd (fun j hj => hsd j hj j hj)) q1
  have hPre_rev : ∀ g ∈ pre.reverse, gateAvoids P_dst g := by
    intro g hg
    rw [List.mem_reverse] at hg
    exact hPre_avoid g hg
  have hcomm := evalRevList_update_comm P_dst pre.reverse hPre_rev q1 q2
    (fun z hz => (hc.1 z (fun j hj heq => hz ⟨j, hj, heq⟩)).symm)
  have hrev : evalRevList pre.reverse q1 = q := evalRevList_reverse pre q
  have hq'_eq : q' = evalRevList pre.reverse q2 := by
    simp [q', fbOutCCU, evalRevList_append, q1, q2]
  rw [hq'_eq]
  refine ⟨?_, ?_⟩
  · intro z hz
    have hzP : ¬ P_dst z := fun ⟨j, hj, heq⟩ => hz j hj heq
    rw [← hcomm.1 z hzP, hrev]
  · intro j hj
    have hjP : P_dst (dst j) := ⟨j, hj, rfl⟩
    have hq2_eq : q2 (dst j) = evalRevList (ccxLoop ctrl src dst L hcs hcd (fun j hj => hsd j hj j hj)) q1 (dst j) := rfl
    rw [hcomm.2 (dst j) hjP, hq2_eq, hc.2 j hj]
    dsimp only [q1]
    rw [hPre_dst j hj, hPre_ctrl]

lemma fin_ne_of_lt {n : ℕ} {a b : Fin n} (h : a.val < b.val) : a ≠ b :=
  Fin.ext_iff.ne.mpr (Nat.ne_of_lt h)

lemma regA_val {r L j : ℕ} (hj : j < L) : (regA_w r L j).val = L + j := by
  simp [regA_w, min_eq_left (Nat.le_of_lt hj)]
lemma regB_val {r L j : ℕ} (hj : j < L) : (regB_w r L j).val = (r + 1) * L + L + j := by
  simp [regB_w, min_eq_left (Nat.le_of_lt hj)]
lemma regH_val {r L j : ℕ} (hj : j < L) : (regH_w r L j).val = 2 * ((r + 1) * L) + L + j := by
  simp [regH_w, min_eq_left (Nat.le_of_lt hj)]
lemma out0_val {r L j : ℕ} (hj : j < L) : (out0_w r L j).val = base_raw r L + j := by
  simp [out0_w, min_eq_left (Nat.le_of_lt hj)]
lemma out1_val {r L j : ℕ} (hj : j < L) : (out1_w r L j).val = base_raw r L + L + j := by
  simp [out1_w, min_eq_left (Nat.le_of_lt hj)]
lemma out2_val {r L j : ℕ} (hj : j < L) : (out2_w r L j).val = base_raw r L + 2 * L + j := by
  simp [out2_w, min_eq_left (Nat.le_of_lt hj)]
lemma out3_val {r L j : ℕ} (hj : j < L) : (out3_w r L j).val = base_raw r L + 3 * L + j := by
  simp [out3_w, min_eq_left (Nat.le_of_lt hj)]
lemma out4_val {r L j : ℕ} (hj : j < L) : (out4_w r L j).val = base_raw r L + 4 * L + j := by
  simp [out4_w, min_eq_left (Nat.le_of_lt hj)]
lemma tmp_val {r L j : ℕ} (hj : j < L) : (tmp_w r L j).val = base_raw r L + 5 * L + j := by
  simp [tmp_w, min_eq_left (Nat.le_of_lt hj)]
lemma outAll_val {r L j : ℕ} (hj : j < 5 * L) : (outAll_w r L j).val = base_raw r L + j := by
  simp [outAll_w, min_eq_left (Nat.le_of_lt hj)]
lemma lowAll_val {r L j : ℕ} (hj : j < 5 * L) : (lowAll_w r L j).val = j := by
  simp [lowAll_w, min_eq_left (Nat.le_of_lt hj)]

lemma mkValidModIO_of_lt {r L : ℕ} (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (hOut_inj : ∀ i < L, ∀ j < L, Out i = Out j → i = j)
    (hX_lt : ∀ j < L, (X j).val < base_raw r L + 6 * L)
    (hY_lt : ∀ j < L, (Y j).val < base_raw r L + 6 * L)
    (hOut_lt : ∀ j < L, (Out j).val < base_raw r L + 6 * L)
    (hXY : ∀ i < L, ∀ j < L, X i ≠ Y j)
    (hXOut : ∀ i < L, ∀ j < L, X i ≠ Out j)
    (hYOut : ∀ i < L, ∀ j < L, Y i ≠ Out j) :
    ValidModIO r L (liftReg L X (zA_w r L)) (liftReg L Y (zB_w r L)) Out where
  Out_inj := hOut_inj
  XY := by
    intro i hi j hj
    by_cases h1 : i < L <;> by_cases h2 : j < L
    · simp only [liftReg, if_pos h1, if_pos h2]
      exact hXY i h1 j h2
    · simp only [liftReg, if_pos h1, if_neg h2]
      exact fin_ne_of_lt (by have := hX_lt i h1; simp only [zB_w]; omega)
    · simp only [liftReg, if_neg h1, if_pos h2]
      exact (fin_ne_of_lt (by have := hY_lt j h2; simp only [zA_w]; omega)).symm
    · simp only [liftReg, if_neg h1, if_neg h2]
      exact fin_ne_of_lt (by simp only [zA_w, zB_w]; omega)
  XOut := by
    intro i hi j hj
    dsimp only [liftReg]
    split_ifs with h1
    · exact hXOut i h1 j hj
    · exact (fin_ne_of_lt (by have := hOut_lt j hj; simp only [zA_w]; omega)).symm
  YOut := by
    intro i hi j hj
    dsimp only [liftReg]
    split_ifs with h2
    · exact hYOut i h2 j hj
    · exact (fin_ne_of_lt (by have := hOut_lt j hj; simp only [zB_w]; omega)).symm
  X_ns := by
    intro i hi hscr
    dsimp only [liftReg] at hscr
    split_ifs at hscr with h1
    · have := hX_lt i h1; simp only [InScratch] at hscr; omega
    · simp only [InScratch, zA_w] at hscr; omega
  Y_ns := by
    intro i hi hscr
    dsimp only [liftReg] at hscr
    split_ifs at hscr with h2
    · have := hY_lt i h2; simp only [InScratch] at hscr; omega
    · simp only [InScratch, zB_w] at hscr; omega
  Out_ns := by
    intro j hj hscr
    have := hOut_lt j hj; simp only [InScratch] at hscr; omega

lemma hIO_AB (r L : ℕ) (hr : 1 ≤ r) :
    ValidModIO r L (liftReg L (regA_w r L) (zA_w r L)) (liftReg L (regB_w r L) (zB_w r L)) (tmp_w r L) := by
  have hW := two_L_le_W r L hr
  apply mkValidModIO_of_lt
  · intro i hi j hj heq; simp only [tmp_w, Fin.ext_iff] at heq
    rw [min_eq_left (by omega), min_eq_left (by omega)] at heq; omega
  · intro j hj; rw [regA_val hj]; simp only [base_raw]; omega
  · intro j hj; rw [regB_val hj]; simp only [base_raw]; omega
  · intro j hj; rw [tmp_val hj]; omega
  · intro i hi j hj; exact fin_ne_of_lt (by rw [regA_val hi, regB_val hj]; omega)
  · intro i hi j hj; exact fin_ne_of_lt (by rw [regA_val hi, tmp_val hj]; simp only [base_raw]; omega)
  · intro i hi j hj; exact fin_ne_of_lt (by rw [regB_val hi, tmp_val hj]; simp only [base_raw]; omega)

lemma hIO_AH (r L : ℕ) (hr : 1 ≤ r) :
    ValidModIO r L (liftReg L (regA_w r L) (zA_w r L)) (liftReg L (regH_w r L) (zB_w r L)) (tmp_w r L) := by
  have hW := two_L_le_W r L hr
  apply mkValidModIO_of_lt
  · intro i hi j hj heq; simp only [tmp_w, Fin.ext_iff] at heq
    rw [min_eq_left (by omega), min_eq_left (by omega)] at heq; omega
  · intro j hj; rw [regA_val hj]; simp only [base_raw]; omega
  · intro j hj; rw [regH_val hj]; simp only [base_raw]; omega
  · intro j hj; rw [tmp_val hj]; omega
  · intro i hi j hj; exact fin_ne_of_lt (by rw [regA_val hi, regH_val hj]; omega)
  · intro i hi j hj; exact fin_ne_of_lt (by rw [regA_val hi, tmp_val hj]; simp only [base_raw]; omega)
  · intro i hi j hj; exact fin_ne_of_lt (by rw [regH_val hi, tmp_val hj]; simp only [base_raw]; omega)

lemma hIO_14 (r L : ℕ) :
    ValidModIO r L (liftReg L (out1_w r L) (zA_w r L)) (liftReg L (out4_w r L) (zB_w r L)) (tmp_w r L) := by
  apply mkValidModIO_of_lt
  · intro i hi j hj heq; simp only [tmp_w, Fin.ext_iff] at heq
    rw [min_eq_left (by omega), min_eq_left (by omega)] at heq; omega
  · intro j hj; rw [out1_val hj]; omega
  · intro j hj; rw [out4_val hj]; omega
  · intro j hj; rw [tmp_val hj]; omega
  · intro i hi j hj; exact fin_ne_of_lt (by rw [out1_val hi, out4_val hj]; omega)
  · intro i hi j hj; exact fin_ne_of_lt (by rw [out1_val hi, tmp_val hj]; omega)
  · intro i hi j hj; exact fin_ne_of_lt (by rw [out4_val hi, tmp_val hj]; omega)

lemma hIO_43 (r L : ℕ) :
    ValidModIO r L (liftReg L (out4_w r L) (zA_w r L)) (liftReg L (out3_w r L) (zB_w r L)) (tmp_w r L) := by
  apply mkValidModIO_of_lt
  · intro i hi j hj heq; simp only [tmp_w, Fin.ext_iff] at heq
    rw [min_eq_left (by omega), min_eq_left (by omega)] at heq; omega
  · intro j hj; rw [out4_val hj]; omega
  · intro j hj; rw [out3_val hj]; omega
  · intro j hj; rw [tmp_val hj]; omega
  · intro i hi j hj; exact (fin_ne_of_lt (by rw [out3_val hj, out4_val hi]; omega)).symm
  · intro i hi j hj; exact fin_ne_of_lt (by rw [out4_val hi, tmp_val hj]; omega)
  · intro i hi j hj; exact fin_ne_of_lt (by rw [out3_val hi, tmp_val hj]; omega)

lemma regA_inj {r L i j : ℕ} (hi : i < L) (hj : j < L) (h : regA_w r L i = regA_w r L j) : i = j := by
  have := congrArg Fin.val h; rw [regA_val hi, regA_val hj] at this; omega
lemma regB_inj {r L i j : ℕ} (hi : i < L) (hj : j < L) (h : regB_w r L i = regB_w r L j) : i = j := by
  have := congrArg Fin.val h; rw [regB_val hi, regB_val hj] at this; omega
lemma regH_inj {r L i j : ℕ} (hi : i < L) (hj : j < L) (h : regH_w r L i = regH_w r L j) : i = j := by
  have := congrArg Fin.val h; rw [regH_val hi, regH_val hj] at this; omega
lemma out0_inj {r L i j : ℕ} (hi : i < L) (hj : j < L) (h : out0_w r L i = out0_w r L j) : i = j := by
  have := congrArg Fin.val h; rw [out0_val hi, out0_val hj] at this; omega
lemma out1_inj {r L i j : ℕ} (hi : i < L) (hj : j < L) (h : out1_w r L i = out1_w r L j) : i = j := by
  have := congrArg Fin.val h; rw [out1_val hi, out1_val hj] at this; omega
lemma out2_inj {r L i j : ℕ} (hi : i < L) (hj : j < L) (h : out2_w r L i = out2_w r L j) : i = j := by
  have := congrArg Fin.val h; rw [out2_val hi, out2_val hj] at this; omega
lemma out3_inj {r L i j : ℕ} (hi : i < L) (hj : j < L) (h : out3_w r L i = out3_w r L j) : i = j := by
  have := congrArg Fin.val h; rw [out3_val hi, out3_val hj] at this; omega
lemma out4_inj {r L i j : ℕ} (hi : i < L) (hj : j < L) (h : out4_w r L i = out4_w r L j) : i = j := by
  have := congrArg Fin.val h; rw [out4_val hi, out4_val hj] at this; omega
lemma tmp_inj {r L i j : ℕ} (hi : i < L) (hj : j < L) (h : tmp_w r L i = tmp_w r L j) : i = j := by
  have := congrArg Fin.val h; rw [tmp_val hi, tmp_val hj] at this; omega

def fbOutFwd (r M L : ℕ) (hr : 1 ≤ r) (hL : 1 ≤ L) : List (RevGate (fbOutW_raw r L)) :=
  have hW : 2 * L ≤ (r + 1) * L := two_L_le_W r L hr
  let wf := wireF_w r L
  let o0 := out0_w r L 0
  let s1 : List (RevGate (fbOutW_raw r L)) :=
    [.cnot wf o0 (fin_ne_of_lt (by rw [out0_val hL]; simp only [wf, wireF_w, base_raw]; omega))]
  let s2 : List (RevGate (fbOutW_raw r L)) :=
    [.x wf] ++
    ccxLoop wf (regA_w r L) (out1_w r L) L
      (fun j hj => (fin_ne_of_lt (by rw [regA_val hj]; simp only [wf, wireF_w]; omega)).symm)
      (fun j hj => fin_ne_of_lt (by rw [out1_val hj]; simp only [wf, wireF_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [regA_val hj, out1_val hj]; simp only [base_raw]; omega)) ++
    ccxLoop wf (regB_w r L) (out2_w r L) L
      (fun j hj => (fin_ne_of_lt (by rw [regB_val hj]; simp only [wf, wireF_w]; omega)).symm)
      (fun j hj => fin_ne_of_lt (by rw [out2_val hj]; simp only [wf, wireF_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [regB_val hj, out2_val hj]; simp only [base_raw]; omega)) ++
    [.x wf]
  let s3 : List (RevGate (fbOutW_raw r L)) :=
    ccxLoop wf (regA_w r L) (out4_w r L) L
      (fun j hj => (fin_ne_of_lt (by rw [regA_val hj]; simp only [wf, wireF_w]; omega)).symm)
      (fun j hj => fin_ne_of_lt (by rw [out4_val hj]; simp only [wf, wireF_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [regA_val hj, out4_val hj]; simp only [base_raw]; omega))
  let s4 : List (RevGate (fbOutW_raw r L)) :=
    fbOutCCU L (addModM M (liftReg L (regA_w r L) (zA_w r L)) (liftReg L (regB_w r L) (zB_w r L))
      (tmp_w r L) (hIO_AB r L hr)) wf (tmp_w r L) (out1_w r L)
      (fun j hj => fin_ne_of_lt (by rw [tmp_val hj]; simp only [wf, wireF_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [out1_val hj]; simp only [wf, wireF_w, base_raw]; omega))
      (fun j hj => (fin_ne_of_lt (by rw [out1_val hj, tmp_val hj]; omega)).symm)
  let s5 : List (RevGate (fbOutW_raw r L)) :=
    fbOutCCU L (subModM M (liftReg L (regA_w r L) (zA_w r L)) (liftReg L (regH_w r L) (zB_w r L))
      (tmp_w r L) (hIO_AH r L hr)) wf (tmp_w r L) (out3_w r L)
      (fun j hj => fin_ne_of_lt (by rw [tmp_val hj]; simp only [wf, wireF_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [out3_val hj]; simp only [wf, wireF_w, base_raw]; omega))
      (fun j hj => (fin_ne_of_lt (by rw [out3_val hj, tmp_val hj]; omega)).symm)
  s1 ++ s2 ++ s3 ++ s4 ++ s5

def fbOutUnc (r M L : ℕ) (hr : 1 ≤ r) (hL : 1 ≤ L) : List (RevGate (fbOutW_raw r L)) :=
  have hW : 2 * L ≤ (r + 1) * L := two_L_le_W r L hr
  let wf := wireF_w r L
  let o0 := out0_w r L 0
  let s6 : List (RevGate (fbOutW_raw r L)) :=
    ccxLoop o0 (out4_w r L) (regA_w r L) L
      (fun j hj => fin_ne_of_lt (by rw [out0_val hL, out4_val hj]; omega))
      (fun j hj => (fin_ne_of_lt (by rw [regA_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
      (fun j hj => (fin_ne_of_lt (by rw [regA_val hj, out4_val hj]; simp only [base_raw]; omega)).symm) ++
    [.x o0] ++
    ccxLoop o0 (out1_w r L) (regA_w r L) L
      (fun j hj => fin_ne_of_lt (by rw [out0_val hL, out1_val hj]; omega))
      (fun j hj => (fin_ne_of_lt (by rw [regA_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
      (fun j hj => (fin_ne_of_lt (by rw [regA_val hj, out1_val hj]; simp only [base_raw]; omega)).symm) ++
    [.x o0]
  let s7 : List (RevGate (fbOutW_raw r L)) :=
    fbOutCCU L (subModM M (liftReg L (out1_w r L) (zA_w r L)) (liftReg L (out4_w r L) (zB_w r L))
      (tmp_w r L) (hIO_14 r L)) o0 (tmp_w r L) (regB_w r L)
      (fun j hj => fin_ne_of_lt (by rw [out0_val hL, tmp_val hj]; omega))
      (fun j hj => (fin_ne_of_lt (by rw [regB_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
      (fun j hj => (fin_ne_of_lt (by rw [regB_val hj, tmp_val hj]; simp only [base_raw]; omega)).symm)
  let s8 : List (RevGate (fbOutW_raw r L)) :=
    [.x o0] ++
    ccxLoop o0 (out2_w r L) (regB_w r L) L
      (fun j hj => fin_ne_of_lt (by rw [out0_val hL, out2_val hj]; omega))
      (fun j hj => (fin_ne_of_lt (by rw [regB_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
      (fun j hj => (fin_ne_of_lt (by rw [regB_val hj, out2_val hj]; simp only [base_raw]; omega)).symm) ++
    [.x o0]
  let s9 : List (RevGate (fbOutW_raw r L)) :=
    fbOutCCU L (subModM M (liftReg L (out4_w r L) (zA_w r L)) (liftReg L (out3_w r L) (zB_w r L))
      (tmp_w r L) (hIO_43 r L)) o0 (tmp_w r L) (regH_w r L)
      (fun j hj => fin_ne_of_lt (by rw [out0_val hL, tmp_val hj]; omega))
      (fun j hj => (fin_ne_of_lt (by rw [regH_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
      (fun j hj => (fin_ne_of_lt (by rw [regH_val hj, tmp_val hj]; simp only [base_raw]; omega)).symm)
  let s10 : List (RevGate (fbOutW_raw r L)) :=
    [.cnot o0 wf (fin_ne_of_lt (by rw [out0_val hL]; simp only [wf, wireF_w, base_raw]; omega)).symm,
     .x (w0_w r L), .x (wW_w r L)]
  s6 ++ s7 ++ s8 ++ s9 ++ s10

def fbOutSwap (r L : ℕ) (hr : 1 ≤ r) : List (RevGate (fbOutW_raw r L)) :=
  have h5 : 5 * L ≤ 3 * ((r + 1) * L) := five_L_le_three_W r L hr
  swapLoop (outAll_w r L) (lowAll_w r L) (5 * L)
    (fun j hj => (fin_ne_of_lt (by rw [lowAll_val hj, outAll_val hj]; simp only [base_raw]; omega)).symm)

def fbOutRev (r M L : ℕ) (hr : 1 ≤ r) (hL : 1 ≤ L) : List (RevGate (fbOutW_raw r L)) :=
  fbOutFwd r M L hr hL ++ fbOutUnc r M L hr hL ++ fbOutSwap r L hr

lemma fbOutRev_length (r M L : ℕ) (hr : 1 ≤ r) (hL : 1 ≤ L) :
    (fbOutRev r M L hr hL).length ≤ 333 * L + 318 := by
  unfold fbOutRev fbOutFwd fbOutUnc fbOutSwap
  simp only [List.length_append, List.length_cons, List.length_nil, ccxLoop_length,
    fbOutCCU_length, swapLoop_length]
  have ha := addModM_length M (liftReg L (regA_w r L) (zA_w r L))
    (liftReg L (regB_w r L) (zB_w r L)) (tmp_w r L) (hIO_AB r L hr)
  have hs1 := subModM_length M (liftReg L (regA_w r L) (zA_w r L))
    (liftReg L (regH_w r L) (zB_w r L)) (tmp_w r L) (hIO_AH r L hr)
  have hs2 := subModM_length M (liftReg L (out1_w r L) (zA_w r L))
    (liftReg L (out4_w r L) (zB_w r L)) (tmp_w r L) (hIO_14 r L)
  have hs3 := subModM_length M (liftReg L (out4_w r L) (zA_w r L))
    (liftReg L (out3_w r L) (zB_w r L)) (tmp_w r L) (hIO_43 r L)
  omega

structure FBIn (r L a b h_val : ℕ) (flag : Bool) (q : Qubits (fbOutW_raw r L)) : Prop where
  w0 : q (w0_w r L) = true
  wW : q (wW_w r L) = true
  wireF : q (wireF_w r L) = flag
  regA : ∀ j < L, q (regA_w r L j) = a.testBit j
  regB : ∀ j < L, q (regB_w r L j) = b.testBit j
  regH : ∀ j < L, q (regH_w r L j) = h_val.testBit j
  rest : ∀ z : Fin (fbOutW_raw r L),
    z ≠ w0_w r L → z ≠ wW_w r L → z ≠ wireF_w r L →
    (∀ j < L, z ≠ regA_w r L j) → (∀ j < L, z ≠ regB_w r L j) →
    (∀ j < L, z ≠ regH_w r L j) → q z = false

structure FBMid (r M L a b h_val : ℕ) (flag : Bool) (q : Qubits (fbOutW_raw r L)) : Prop where
  w0 : q (w0_w r L) = true
  wW : q (wW_w r L) = true
  wireF : q (wireF_w r L) = flag
  regA : ∀ j < L, q (regA_w r L j) = a.testBit j
  regB : ∀ j < L, q (regB_w r L j) = b.testBit j
  regH : ∀ j < L, q (regH_w r L j) = h_val.testBit j
  out0_0 : q (out0_w r L 0) = flag
  out0_pos : ∀ j, 1 ≤ j → j < L → q (out0_w r L j) = false
  out1 : ∀ j < L, q (out1_w r L j) = if flag then ((a + b) % M).testBit j else a.testBit j
  out2 : ∀ j < L, q (out2_w r L j) = if flag then false else b.testBit j
  out3 : ∀ j < L, q (out3_w r L j) = if flag then ((M + a - h_val) % M).testBit j else false
  out4 : ∀ j < L, q (out4_w r L j) = if flag then a.testBit j else false
  high : ∀ z : Fin (fbOutW_raw r L), base_raw r L + 5 * L ≤ z.val → q z = false
  low_rest : ∀ z : Fin (fbOutW_raw r L), z.val < base_raw r L →
    z ≠ w0_w r L → z ≠ wW_w r L → z ≠ wireF_w r L →
    (∀ j < L, z ≠ regA_w r L j) → (∀ j < L, z ≠ regB_w r L j) →
    (∀ j < L, z ≠ regH_w r L j) → q z = false

lemma fbOutFwd_spec (r M L a b h_val : ℕ) (flag : Bool)
    (hr : 1 ≤ r) (hL : 1 ≤ L) (hM1 : 1 ≤ M) (hML : M < 2 ^ L)
    (ha : a < M) (hb : b < M) (hh : h_val < M) (q : Qubits (fbOutW_raw r L))
    (hin : FBIn r L a b h_val flag q) :
    FBMid r M L a b h_val flag (evalRevList (fbOutFwd r M L hr hL) q) := by
  have hW : 2 * L ≤ (r + 1) * L := two_L_le_W r L hr
  have hq_base : ∀ z : Fin (fbOutW_raw r L), base_raw r L ≤ z.val → q z = false := by
    intro z hz
    apply hin.rest z
    · exact (fin_ne_of_lt (by simp only [w0_w, base_raw] at hz ⊢; omega)).symm
    · exact (fin_ne_of_lt (by simp only [wW_w, base_raw] at hz ⊢; omega)).symm
    · exact (fin_ne_of_lt (by simp only [wireF_w, base_raw] at hz ⊢; omega)).symm
    · intro j hj; exact (fin_ne_of_lt (by rw [regA_val hj]; simp only [base_raw] at hz ⊢; omega)).symm
    · intro j hj; exact (fin_ne_of_lt (by rw [regB_val hj]; simp only [base_raw] at hz ⊢; omega)).symm
    · intro j hj; exact (fin_ne_of_lt (by rw [regH_val hj]; simp only [base_raw] at hz ⊢; omega)).symm
  let wf := wireF_w r L
  let o0 := out0_w r L 0
  let q1 := evalRev (.cnot wf o0 (fin_ne_of_lt (by rw [out0_val hL]; simp only [wf, wireF_w, base_raw]; omega))) q
  have hq1_o0 : q1 o0 = flag := by
    dsimp only [q1]
    rw [evalRev_cnot, Function.update_self, hq_base o0 (by rw [out0_val hL]; omega), hin.wireF]
    simp
  have hq1_other : ∀ z, z ≠ o0 → q1 z = q z := fun z hz => by simp [q1, hz]
  let c2a := ccxLoop wf (regA_w r L) (out1_w r L) L
      (fun j hj => (fin_ne_of_lt (by rw [regA_val hj]; simp only [wf, wireF_w]; omega)).symm)
      (fun j hj => fin_ne_of_lt (by rw [out1_val hj]; simp only [wf, wireF_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [regA_val hj, out1_val hj]; simp only [base_raw]; omega))
  let c2b := ccxLoop wf (regB_w r L) (out2_w r L) L
      (fun j hj => (fin_ne_of_lt (by rw [regB_val hj]; simp only [wf, wireF_w]; omega)).symm)
      (fun j hj => fin_ne_of_lt (by rw [out2_val hj]; simp only [wf, wireF_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [regB_val hj, out2_val hj]; simp only [base_raw]; omega))
  let q2_0 := evalRev (.x wf) q1
  let q2_1 := evalRevList c2a q2_0
  let q2_2 := evalRevList c2b q2_1
  let q2 := evalRev (.x wf) q2_2
  have hc2a := ccxLoop_spec wf (regA_w r L) (out1_w r L) L
    (fun j hj => (fin_ne_of_lt (by rw [regA_val hj]; simp only [wf, wireF_w]; omega)).symm)
    (fun j hj => fin_ne_of_lt (by rw [out1_val hj]; simp only [wf, wireF_w, base_raw]; omega))
    (fun i hi j hj => fin_ne_of_lt (by rw [regA_val hi, out1_val hj]; simp only [base_raw]; omega))
    (fun _ hi _ hj => out1_inj hi hj) q2_0
  have hc2b := ccxLoop_spec wf (regB_w r L) (out2_w r L) L
    (fun j hj => (fin_ne_of_lt (by rw [regB_val hj]; simp only [wf, wireF_w]; omega)).symm)
    (fun j hj => fin_ne_of_lt (by rw [out2_val hj]; simp only [wf, wireF_w, base_raw]; omega))
    (fun i hi j hj => fin_ne_of_lt (by rw [regB_val hi, out2_val hj]; simp only [base_raw]; omega))
    (fun _ hi _ hj => out2_inj hi hj) q2_1
  have hq2_non : ∀ z, (∀ j < L, z ≠ out1_w r L j) → (∀ j < L, z ≠ out2_w r L j) → q2 z = q1 z := by
    intro z hz1 hz2
    have h2z : q2_2 z = q2_1 z := hc2b.1 z hz2
    have h1z : q2_1 z = q2_0 z := hc2a.1 z hz1
    by_cases hzw : z = wf
    · rw [hzw]
      have h2w : q2_2 wf = q2_1 wf := hzw ▸ h2z
      have h1w : q2_1 wf = q2_0 wf := hzw ▸ h1z
      dsimp only [q2]; rw [evalRev_x, Function.update_self, h2w, h1w]
      dsimp only [q2_0]; rw [evalRev_x, Function.update_self, Bool.not_not]
    · dsimp only [q2]; rw [evalRev_x, Function.update_of_ne hzw, h2z, h1z]
      dsimp only [q2_0]; rw [evalRev_x, Function.update_of_ne hzw]
  have hq2_out1 : ∀ j < L, q2 (out1_w r L j) = if flag then false else a.testBit j := by
    intro j hj
    have hne_w : out1_w r L j ≠ wf := (fin_ne_of_lt (by rw [out1_val hj]; simp only [wf, wireF_w, base_raw]; omega)).symm
    have hne_o0 : out1_w r L j ≠ o0 := (fin_ne_of_lt (by rw [out0_val hL, out1_val hj]; omega)).symm
    have hne_o : ∀ t < L, out1_w r L j ≠ out2_w r L t :=
      fun t ht => fin_ne_of_lt (by rw [out1_val hj, out2_val ht]; omega)
    dsimp only [q2]
    rw [evalRev_x, Function.update_of_ne hne_w, show q2_2 (out1_w r L j) = q2_1 (out1_w r L j) from hc2b.1 _ hne_o]
    dsimp only [q2_1]
    rw [hc2a.2 j hj]
    have h20o : q2_0 (out1_w r L j) = false := by
      dsimp only [q2_0]; rw [evalRev_x, Function.update_of_ne hne_w, hq1_other _ hne_o0,
        hq_base _ (by rw [out1_val hj]; omega)]
    have h20w : q2_0 wf = !flag := by
      have hne_wf_o0 : wf ≠ o0 := fin_ne_of_lt (by rw [out0_val hL]; simp only [wf, wireF_w, base_raw]; omega)
      dsimp only [q2_0]; rw [evalRev_x, Function.update_self, hq1_other _ hne_wf_o0, hin.wireF]
    have h20a : q2_0 (regA_w r L j) = a.testBit j := by
      have hne_aw : regA_w r L j ≠ wf := fin_ne_of_lt (by rw [regA_val hj]; simp only [wf, wireF_w]; omega)
      have hne_ao : regA_w r L j ≠ o0 := fin_ne_of_lt (by rw [regA_val hj, out0_val hL]; simp only [base_raw]; omega)
      dsimp only [q2_0]; rw [evalRev_x, Function.update_of_ne hne_aw, hq1_other _ hne_ao, hin.regA j hj]
    rw [h20o, h20w, h20a]; cases flag <;> simp
  have hq2_out2 : ∀ j < L, q2 (out2_w r L j) = if flag then false else b.testBit j := by
    intro j hj
    have hne_w : out2_w r L j ≠ wf := (fin_ne_of_lt (by rw [out2_val hj]; simp only [wf, wireF_w, base_raw]; omega)).symm
    have hne_o0 : out2_w r L j ≠ o0 := (fin_ne_of_lt (by rw [out0_val hL, out2_val hj]; omega)).symm
    have hne_o : ∀ t < L, out2_w r L j ≠ out1_w r L t :=
      fun t ht => (fin_ne_of_lt (by rw [out1_val ht, out2_val hj]; omega)).symm
    dsimp only [q2]
    rw [evalRev_x, Function.update_of_ne hne_w]
    dsimp only [q2_2]
    rw [hc2b.2 j hj]
    have h21o : q2_1 (out2_w r L j) = false := by
      rw [show q2_1 (out2_w r L j) = q2_0 (out2_w r L j) from hc2a.1 _ hne_o]
      dsimp only [q2_0]; rw [evalRev_x, Function.update_of_ne hne_w, hq1_other _ hne_o0,
        hq_base _ (by rw [out2_val hj]; omega)]
    have h21w : q2_1 wf = !flag := by
      have hne_wf_o0 : wf ≠ o0 := fin_ne_of_lt (by rw [out0_val hL]; simp only [wf, wireF_w, base_raw]; omega)
      rw [show q2_1 wf = q2_0 wf from hc2a.1 _ (fun t ht => fin_ne_of_lt (by rw [out1_val ht]; simp only [wf, wireF_w, base_raw]; omega))]
      dsimp only [q2_0]; rw [evalRev_x, Function.update_self, hq1_other _ hne_wf_o0, hin.wireF]
    have h21b : q2_1 (regB_w r L j) = b.testBit j := by
      have hne_bw : regB_w r L j ≠ wf := fin_ne_of_lt (by rw [regB_val hj]; simp only [wf, wireF_w]; omega)
      have hne_bo : regB_w r L j ≠ o0 := fin_ne_of_lt (by rw [regB_val hj, out0_val hL]; simp only [base_raw]; omega)
      rw [show q2_1 (regB_w r L j) = q2_0 (regB_w r L j) from hc2a.1 _ (fun t ht => fin_ne_of_lt (by rw [regB_val hj, out1_val ht]; simp only [base_raw]; omega))]
      dsimp only [q2_0]; rw [evalRev_x, Function.update_of_ne hne_bw, hq1_other _ hne_bo, hin.regB j hj]
    rw [h21o, h21w, h21b]; cases flag <;> simp
  let c3 := ccxLoop wf (regA_w r L) (out4_w r L) L
      (fun j hj => (fin_ne_of_lt (by rw [regA_val hj]; simp only [wf, wireF_w]; omega)).symm)
      (fun j hj => fin_ne_of_lt (by rw [out4_val hj]; simp only [wf, wireF_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [regA_val hj, out4_val hj]; simp only [base_raw]; omega))
  let q3 := evalRevList c3 q2
  have hc3 := ccxLoop_spec wf (regA_w r L) (out4_w r L) L
    (fun j hj => (fin_ne_of_lt (by rw [regA_val hj]; simp only [wf, wireF_w]; omega)).symm)
    (fun j hj => fin_ne_of_lt (by rw [out4_val hj]; simp only [wf, wireF_w, base_raw]; omega))
    (fun i hi j hj => fin_ne_of_lt (by rw [regA_val hi, out4_val hj]; simp only [base_raw]; omega))
    (fun _ hi _ hj => out4_inj hi hj) q2
  have hq3_wf : q3 wf = flag := by
    rw [show q3 wf = q2 wf from hc3.1 _ (fun t ht => fin_ne_of_lt (by rw [out4_val ht]; simp only [wf, wireF_w, base_raw]; omega)),
      hq2_non _ (fun t ht => fin_ne_of_lt (by rw [out1_val ht]; simp only [wf, wireF_w, base_raw]; omega))
        (fun t ht => fin_ne_of_lt (by rw [out2_val ht]; simp only [wf, wireF_w, base_raw]; omega)),
      hq1_other _ (fin_ne_of_lt (by rw [out0_val hL]; simp only [wf, wireF_w, base_raw]; omega)), hin.wireF]
  have hq3_regA : ∀ j < L, q3 (regA_w r L j) = a.testBit j := fun j hj => by
    rw [show q3 (regA_w r L j) = q2 (regA_w r L j) from hc3.1 _ (fun t ht => fin_ne_of_lt (by rw [regA_val hj, out4_val ht]; simp only [base_raw]; omega)),
      hq2_non _ (fun t ht => fin_ne_of_lt (by rw [regA_val hj, out1_val ht]; simp only [base_raw]; omega))
        (fun t ht => fin_ne_of_lt (by rw [regA_val hj, out2_val ht]; simp only [base_raw]; omega)),
      hq1_other _ (fin_ne_of_lt (by rw [regA_val hj, out0_val hL]; simp only [base_raw]; omega)), hin.regA j hj]
  have hq3_regB : ∀ j < L, q3 (regB_w r L j) = b.testBit j := fun j hj => by
    rw [show q3 (regB_w r L j) = q2 (regB_w r L j) from hc3.1 _ (fun t ht => fin_ne_of_lt (by rw [regB_val hj, out4_val ht]; simp only [base_raw]; omega)),
      hq2_non _ (fun t ht => fin_ne_of_lt (by rw [regB_val hj, out1_val ht]; simp only [base_raw]; omega))
        (fun t ht => fin_ne_of_lt (by rw [regB_val hj, out2_val ht]; simp only [base_raw]; omega)),
      hq1_other _ (fin_ne_of_lt (by rw [regB_val hj, out0_val hL]; simp only [base_raw]; omega)), hin.regB j hj]
  have hq3_regH : ∀ j < L, q3 (regH_w r L j) = h_val.testBit j := fun j hj => by
    rw [show q3 (regH_w r L j) = q2 (regH_w r L j) from hc3.1 _ (fun t ht => fin_ne_of_lt (by rw [regH_val hj, out4_val ht]; simp only [base_raw]; omega)),
      hq2_non _ (fun t ht => fin_ne_of_lt (by rw [regH_val hj, out1_val ht]; simp only [base_raw]; omega))
        (fun t ht => fin_ne_of_lt (by rw [regH_val hj, out2_val ht]; simp only [base_raw]; omega)),
      hq1_other _ (fin_ne_of_lt (by rw [regH_val hj, out0_val hL]; simp only [base_raw]; omega)), hin.regH j hj]
  have hq3_scr : ∀ z, InScratch r L z → q3 z = false := fun z hz => by
    rw [show q3 z = q2 z from hc3.1 _ (fun t ht => (fin_ne_of_lt (by rw [out4_val ht]; simp only [InScratch] at hz; omega)).symm),
      hq2_non _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht]; simp only [InScratch] at hz; omega)).symm)
        (fun t ht => (fin_ne_of_lt (by rw [out2_val ht]; simp only [InScratch] at hz; omega)).symm),
      hq1_other _ (fun heq => by dsimp only [o0] at heq; simp only [InScratch] at hz; rw [heq, out0_val hL] at hz; omega),
      hq_base z (by simp only [InScratch] at hz; omega)]
  have hq3_tmp : ∀ j < L, q3 (tmp_w r L j) = false := fun j hj => by
    rw [show q3 (tmp_w r L j) = q2 (tmp_w r L j) from hc3.1 _ (fun t ht => (fin_ne_of_lt (by rw [out4_val ht, tmp_val hj]; omega)).symm),
      hq2_non _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht, tmp_val hj]; omega)).symm)
        (fun t ht => (fin_ne_of_lt (by rw [out2_val ht, tmp_val hj]; omega)).symm),
      hq1_other _ (fin_ne_of_lt (by rw [out0_val hL, tmp_val hj]; omega)).symm,
      hq_base _ (by rw [tmp_val hj]; omega)]
  have hq3_zA : q3 (zA_w r L) = false := by
    rw [show q3 (zA_w r L) = q2 (zA_w r L) from hc3.1 _ (fun t ht => (fin_ne_of_lt (by rw [out4_val ht]; simp only [zA_w]; omega)).symm),
      hq2_non _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht]; simp only [zA_w]; omega)).symm)
        (fun t ht => (fin_ne_of_lt (by rw [out2_val ht]; simp only [zA_w]; omega)).symm),
      hq1_other _ (fin_ne_of_lt (by rw [out0_val hL]; simp only [zA_w]; omega)).symm,
      hq_base _ (by simp only [zA_w]; omega)]
  have hq3_zB : q3 (zB_w r L) = false := by
    rw [show q3 (zB_w r L) = q2 (zB_w r L) from hc3.1 _ (fun t ht => (fin_ne_of_lt (by rw [out4_val ht]; simp only [zB_w]; omega)).symm),
      hq2_non _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht]; simp only [zB_w]; omega)).symm)
        (fun t ht => (fin_ne_of_lt (by rw [out2_val ht]; simp only [zB_w]; omega)).symm),
      hq1_other _ (fin_ne_of_lt (by rw [out0_val hL]; simp only [zB_w]; omega)).symm,
      hq_base _ (by simp only [zB_w]; omega)]
  have hML' : M < 2 ^ (L + 1) := lt_trans hML (by rw [pow_succ]; omega)
  let pre4 := addModM M (liftReg L (regA_w r L) (zA_w r L)) (liftReg L (regB_w r L) (zB_w r L))
      (tmp_w r L) (hIO_AB r L hr)
  have hadd4 := addModM_spec M hM1 hML _ _ (tmp_w r L) (hIO_AB r L hr) q3 hq3_scr hq3_tmp
    (by rw [regVal_liftReg L _ _ q3 hq3_zA]
        rw [regVal_eq_of_testBit (lt_trans ha hML) (fun j hj => hq3_regA j hj)]; exact ha)
    (by rw [regVal_liftReg L _ _ q3 hq3_zB]
        rw [regVal_eq_of_testBit (lt_trans hb hML) (fun j hj => hq3_regB j hj)]; exact hb)
  have hpre4_av : ∀ g ∈ pre4, gateAvoids (fun z => ∃ j < L, z = out1_w r L j) g := by
    apply addModM_avoid
    · intro i hi ⟨j, hj, heq⟩; dsimp only [liftReg] at heq; split_ifs at heq with h1
      · exact fin_ne_of_lt (by rw [regA_val h1, out1_val hj]; simp only [base_raw]; omega) heq
      · exact (fin_ne_of_lt (by rw [out1_val hj]; simp only [zA_w]; omega)).symm heq
    · intro i hi ⟨j, hj, heq⟩; dsimp only [liftReg] at heq; split_ifs at heq with h1
      · exact fin_ne_of_lt (by rw [regB_val h1, out1_val hj]; simp only [base_raw]; omega) heq
      · exact (fin_ne_of_lt (by rw [out1_val hj]; simp only [zB_w]; omega)).symm heq
    · intro i hi ⟨j, hj, heq⟩
      exact (fin_ne_of_lt (by rw [out1_val hj, tmp_val hi]; omega)).symm heq
    · rintro z hz ⟨j, hj, heq⟩; simp only [InScratch] at hz; rw [heq, out1_val hj] at hz; omega
  have hccu4 := fbOutCCU_spec L pre4 wf (tmp_w r L) (out1_w r L)
    (fun j hj => fin_ne_of_lt (by rw [tmp_val hj]; simp only [wf, wireF_w, base_raw]; omega))
    (fun j hj => fin_ne_of_lt (by rw [out1_val hj]; simp only [wf, wireF_w, base_raw]; omega))
    (fun i hi j hj => (fin_ne_of_lt (by rw [out1_val hj, tmp_val hi]; omega)).symm)
    (fun _ hi _ hj => out1_inj hi hj) hpre4_av q3
    (hadd4.1 wf (fun j hj => fin_ne_of_lt (by rw [tmp_val hj]; simp only [wf, wireF_w, base_raw]; omega)))
    (fun j hj => hadd4.1 (out1_w r L j) (fun t ht => fin_ne_of_lt (by rw [out1_val hj, tmp_val ht]; omega)))
  let q4 := evalRevList (fbOutCCU L pre4 wf (tmp_w r L) (out1_w r L)
    (fun j hj => fin_ne_of_lt (by rw [tmp_val hj]; simp only [wf, wireF_w, base_raw]; omega))
    (fun j hj => fin_ne_of_lt (by rw [out1_val hj]; simp only [wf, wireF_w, base_raw]; omega))
    (fun j hj => (fin_ne_of_lt (by rw [out1_val hj, tmp_val hj]; omega)).symm)) q3
  have hq4_non : ∀ z, (∀ j < L, z ≠ out1_w r L j) → q4 z = q3 z := hccu4.1
  have hq4_wf : q4 wf = flag := by
    rw [hq4_non _ (fun t ht => fin_ne_of_lt (by rw [out1_val ht]; simp only [wf, wireF_w, base_raw]; omega)), hq3_wf]
  have hq4_scr : ∀ z, InScratch r L z → q4 z = false := fun z hz => by
    rw [hq4_non z (fun t ht => (fin_ne_of_lt (by rw [out1_val ht]; simp only [InScratch] at hz; omega)).symm), hq3_scr z hz]
  have hq4_tmp : ∀ j < L, q4 (tmp_w r L j) = false := fun j hj => by
    rw [hq4_non _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht, tmp_val hj]; omega)).symm), hq3_tmp j hj]
  have hq4_zA : q4 (zA_w r L) = false := by
    rw [hq4_non _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht]; simp only [zA_w]; omega)).symm), hq3_zA]
  have hq4_zB : q4 (zB_w r L) = false := by
    rw [hq4_non _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht]; simp only [zB_w]; omega)).symm), hq3_zB]
  have hq4_regA : ∀ j < L, q4 (regA_w r L j) = a.testBit j := fun j hj => by
    rw [hq4_non _ (fun t ht => fin_ne_of_lt (by rw [regA_val hj, out1_val ht]; simp only [base_raw]; omega)), hq3_regA j hj]
  have hq4_regH : ∀ j < L, q4 (regH_w r L j) = h_val.testBit j := fun j hj => by
    rw [hq4_non _ (fun t ht => fin_ne_of_lt (by rw [regH_val hj, out1_val ht]; simp only [base_raw]; omega)), hq3_regH j hj]
  let pre5 := subModM M (liftReg L (regA_w r L) (zA_w r L)) (liftReg L (regH_w r L) (zB_w r L))
      (tmp_w r L) (hIO_AH r L hr)
  have hsub5 := subModM_spec M hM1 hML _ _ (tmp_w r L) (hIO_AH r L hr) q4 hq4_scr hq4_tmp
    (by rw [regVal_liftReg L _ _ q4 hq4_zA]
        rw [regVal_eq_of_testBit (lt_trans ha hML) (fun j hj => hq4_regA j hj)]; exact ha)
    (by rw [regVal_liftReg L _ _ q4 hq4_zB]
        rw [regVal_eq_of_testBit (lt_trans hh hML) (fun j hj => hq4_regH j hj)]; exact hh)
  have hpre5_av : ∀ g ∈ pre5, gateAvoids (fun z => ∃ j < L, z = out3_w r L j) g := by
    apply subModM_avoid
    · intro i hi ⟨j, hj, heq⟩; dsimp only [liftReg] at heq; split_ifs at heq with h1
      · exact fin_ne_of_lt (by rw [regA_val h1, out3_val hj]; simp only [base_raw]; omega) heq
      · exact (fin_ne_of_lt (by rw [out3_val hj]; simp only [zA_w]; omega)).symm heq
    · intro i hi ⟨j, hj, heq⟩; dsimp only [liftReg] at heq; split_ifs at heq with h1
      · exact fin_ne_of_lt (by rw [regH_val h1, out3_val hj]; simp only [base_raw]; omega) heq
      · exact (fin_ne_of_lt (by rw [out3_val hj]; simp only [zB_w]; omega)).symm heq
    · intro i hi ⟨j, hj, heq⟩
      exact (fin_ne_of_lt (by rw [out3_val hj, tmp_val hi]; omega)).symm heq
    · rintro z hz ⟨j, hj, heq⟩; simp only [InScratch] at hz; rw [heq, out3_val hj] at hz; omega
  have hccu5 := fbOutCCU_spec L pre5 wf (tmp_w r L) (out3_w r L)
    (fun j hj => fin_ne_of_lt (by rw [tmp_val hj]; simp only [wf, wireF_w, base_raw]; omega))
    (fun j hj => fin_ne_of_lt (by rw [out3_val hj]; simp only [wf, wireF_w, base_raw]; omega))
    (fun i hi j hj => (fin_ne_of_lt (by rw [out3_val hj, tmp_val hi]; omega)).symm)
    (fun _ hi _ hj => out3_inj hi hj) hpre5_av q4
    (hsub5.1 wf (fun j hj => fin_ne_of_lt (by rw [tmp_val hj]; simp only [wf, wireF_w, base_raw]; omega)))
    (fun j hj => hsub5.1 (out3_w r L j) (fun t ht => fin_ne_of_lt (by rw [out3_val hj, tmp_val ht]; omega)))
  let q5 := evalRevList (fbOutCCU L pre5 wf (tmp_w r L) (out3_w r L)
    (fun j hj => fin_ne_of_lt (by rw [tmp_val hj]; simp only [wf, wireF_w, base_raw]; omega))
    (fun j hj => fin_ne_of_lt (by rw [out3_val hj]; simp only [wf, wireF_w, base_raw]; omega))
    (fun j hj => (fin_ne_of_lt (by rw [out3_val hj, tmp_val hj]; omega)).symm)) q4
  have hq5_eq : evalRevList (fbOutFwd r M L hr hL) q = q5 := by
    simp only [fbOutFwd, evalRevList_append, evalRevList_cons, evalRevList_nil]
    rfl
  rw [hq5_eq]
  have hq5_non3 : ∀ z, (∀ j < L, z ≠ out3_w r L j) → q5 z = q4 z := hccu5.1
  have hq5_non13 : ∀ z, (∀ j < L, z ≠ out1_w r L j) → (∀ j < L, z ≠ out3_w r L j) → q5 z = q3 z := by
    intro z h1 h3; rw [hq5_non3 z h3, hq4_non z h1]
  have hq5_non134 : ∀ z, (∀ j < L, z ≠ out1_w r L j) → (∀ j < L, z ≠ out3_w r L j) →
      (∀ j < L, z ≠ out4_w r L j) → q5 z = q2 z := by
    intro z h1 h3 h4; rw [hq5_non13 z h1 h3]; exact hc3.1 z h4
  have hq5_non_all : ∀ z, (∀ j < L, z ≠ out1_w r L j) → (∀ j < L, z ≠ out2_w r L j) →
      (∀ j < L, z ≠ out3_w r L j) → (∀ j < L, z ≠ out4_w r L j) → z ≠ o0 → q5 z = q z := by
    intro z h1 h2 h3 h4 ho
    rw [hq5_non134 z h1 h3 h4, hq2_non z h1 h2, hq1_other z ho]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hq5_non_all _ (fun j hj => fin_ne_of_lt (by rw [out1_val hj]; simp only [w0_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [out2_val hj]; simp only [w0_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [out3_val hj]; simp only [w0_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [out4_val hj]; simp only [w0_w, base_raw]; omega))
      (fin_ne_of_lt (by rw [out0_val hL]; simp only [w0_w, base_raw]; omega))]; exact hin.w0
  · rw [hq5_non_all _ (fun j hj => fin_ne_of_lt (by rw [out1_val hj]; simp only [wW_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [out2_val hj]; simp only [wW_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [out3_val hj]; simp only [wW_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [out4_val hj]; simp only [wW_w, base_raw]; omega))
      (fin_ne_of_lt (by rw [out0_val hL]; simp only [wW_w, base_raw]; omega))]; exact hin.wW
  · rw [hq5_non_all _ (fun j hj => fin_ne_of_lt (by rw [out1_val hj]; simp only [wireF_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [out2_val hj]; simp only [wireF_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [out3_val hj]; simp only [wireF_w, base_raw]; omega))
      (fun j hj => fin_ne_of_lt (by rw [out4_val hj]; simp only [wireF_w, base_raw]; omega))
      (fin_ne_of_lt (by rw [out0_val hL]; simp only [wireF_w, base_raw]; omega))]; exact hin.wireF
  · intro j hj
    rw [hq5_non_all _ (fun t ht => fin_ne_of_lt (by rw [regA_val hj, out1_val ht]; simp only [base_raw]; omega))
      (fun t ht => fin_ne_of_lt (by rw [regA_val hj, out2_val ht]; simp only [base_raw]; omega))
      (fun t ht => fin_ne_of_lt (by rw [regA_val hj, out3_val ht]; simp only [base_raw]; omega))
      (fun t ht => fin_ne_of_lt (by rw [regA_val hj, out4_val ht]; simp only [base_raw]; omega))
      (fin_ne_of_lt (by rw [regA_val hj, out0_val hL]; simp only [base_raw]; omega))]; exact hin.regA j hj
  · intro j hj
    rw [hq5_non_all _ (fun t ht => fin_ne_of_lt (by rw [regB_val hj, out1_val ht]; simp only [base_raw]; omega))
      (fun t ht => fin_ne_of_lt (by rw [regB_val hj, out2_val ht]; simp only [base_raw]; omega))
      (fun t ht => fin_ne_of_lt (by rw [regB_val hj, out3_val ht]; simp only [base_raw]; omega))
      (fun t ht => fin_ne_of_lt (by rw [regB_val hj, out4_val ht]; simp only [base_raw]; omega))
      (fin_ne_of_lt (by rw [regB_val hj, out0_val hL]; simp only [base_raw]; omega))]; exact hin.regB j hj
  · intro j hj
    rw [hq5_non_all _ (fun t ht => fin_ne_of_lt (by rw [regH_val hj, out1_val ht]; simp only [base_raw]; omega))
      (fun t ht => fin_ne_of_lt (by rw [regH_val hj, out2_val ht]; simp only [base_raw]; omega))
      (fun t ht => fin_ne_of_lt (by rw [regH_val hj, out3_val ht]; simp only [base_raw]; omega))
      (fun t ht => fin_ne_of_lt (by rw [regH_val hj, out4_val ht]; simp only [base_raw]; omega))
      (fin_ne_of_lt (by rw [regH_val hj, out0_val hL]; simp only [base_raw]; omega))]; exact hin.regH j hj
  · rw [hq5_non134 _ (fun t ht => fin_ne_of_lt (by rw [out0_val hL, out1_val ht]; omega))
      (fun t ht => fin_ne_of_lt (by rw [out0_val hL, out3_val ht]; omega))
      (fun t ht => fin_ne_of_lt (by rw [out0_val hL, out4_val ht]; omega)),
      hq2_non _ (fun t ht => fin_ne_of_lt (by rw [out0_val hL, out1_val ht]; omega))
        (fun t ht => fin_ne_of_lt (by rw [out0_val hL, out2_val ht]; omega)), hq1_o0]
  · intro j hj1 hjL
    rw [hq5_non_all _ (fun t ht => fin_ne_of_lt (by rw [out0_val hjL, out1_val ht]; omega))
      (fun t ht => fin_ne_of_lt (by rw [out0_val hjL, out2_val ht]; omega))
      (fun t ht => fin_ne_of_lt (by rw [out0_val hjL, out3_val ht]; omega))
      (fun t ht => fin_ne_of_lt (by rw [out0_val hjL, out4_val ht]; omega))
      (fin_ne_of_lt (by rw [out0_val hL, out0_val hjL]; omega)).symm]
    exact hq_base _ (by rw [out0_val hjL]; omega)
  · intro j hj
    rw [hq5_non3 _ (fun t ht => fin_ne_of_lt (by rw [out1_val hj, out3_val ht]; omega))]
    dsimp only [q4]
    rw [hccu4.2 j hj]
    have h3o : q3 (out1_w r L j) = q2 (out1_w r L j) :=
      hc3.1 _ (fun t ht => fin_ne_of_lt (by rw [out1_val hj, out4_val ht]; omega))
    rw [h3o, hq2_out1 j hj, hq3_wf]
    have hadd_j := hadd4.2.2 j hj
    have ha_val : regVal q3 (liftReg L (regA_w r L) (zA_w r L)) (L + 1) = a := by
      rw [regVal_liftReg L _ _ q3 hq3_zA]
      exact regVal_eq_of_testBit (lt_trans ha hML) (fun t ht => hq3_regA t ht)
    have hb_val : regVal q3 (liftReg L (regB_w r L) (zB_w r L)) (L + 1) = b := by
      rw [regVal_liftReg L _ _ q3 hq3_zB]
      exact regVal_eq_of_testBit (lt_trans hb hML) (fun t ht => hq3_regB t ht)
    rw [ha_val, hb_val] at hadd_j
    rw [hadd_j]; cases flag <;> simp
  · intro j hj
    rw [hq5_non134 _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht, out2_val hj]; omega)).symm)
      (fun t ht => fin_ne_of_lt (by rw [out2_val hj, out3_val ht]; omega))
      (fun t ht => fin_ne_of_lt (by rw [out2_val hj, out4_val ht]; omega)), hq2_out2 j hj]
  · intro j hj
    dsimp only [q5]
    rw [hccu5.2 j hj]
    have h4o : q4 (out3_w r L j) = false := by
      rw [hq4_non _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht, out3_val hj]; omega)).symm)]
      dsimp only [q3]
      rw [hc3.1 _ (fun t ht => fin_ne_of_lt (by rw [out3_val hj, out4_val ht]; omega)),
        hq2_non _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht, out3_val hj]; omega)).symm)
          (fun t ht => (fin_ne_of_lt (by rw [out2_val ht, out3_val hj]; omega)).symm),
        hq1_other _ (fin_ne_of_lt (by rw [out0_val hL, out3_val hj]; omega)).symm,
        hq_base _ (by rw [out3_val hj]; omega)]
    rw [h4o, hq4_wf, Bool.false_xor]
    have hsub_j := hsub5.2.2 j hj
    have ha_val : regVal q4 (liftReg L (regA_w r L) (zA_w r L)) (L + 1) = a := by
      rw [regVal_liftReg L _ _ q4 hq4_zA]
      exact regVal_eq_of_testBit (lt_trans ha hML) (fun t ht => hq4_regA t ht)
    have hh_val : regVal q4 (liftReg L (regH_w r L) (zB_w r L)) (L + 1) = h_val := by
      rw [regVal_liftReg L _ _ q4 hq4_zB]
      exact regVal_eq_of_testBit (lt_trans hh hML) (fun t ht => hq4_regH t ht)
    rw [ha_val, hh_val] at hsub_j
    rw [hsub_j]; cases flag <;> simp
  · intro j hj
    rw [hq5_non13 _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht, out4_val hj]; omega)).symm)
      (fun t ht => (fin_ne_of_lt (by rw [out3_val ht, out4_val hj]; omega)).symm)]
    dsimp only [q3]; rw [hc3.2 j hj]
    have h2o : q2 (out4_w r L j) = false := by
      rw [hq2_non _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht, out4_val hj]; omega)).symm)
        (fun t ht => (fin_ne_of_lt (by rw [out2_val ht, out4_val hj]; omega)).symm),
        hq1_other _ (fin_ne_of_lt (by rw [out0_val hL, out4_val hj]; omega)).symm,
        hq_base _ (by rw [out4_val hj]; omega)]
    have h2w : q2 wf = flag := by
      rw [hq2_non _ (fun t ht => fin_ne_of_lt (by rw [out1_val ht]; simp only [wf, wireF_w, base_raw]; omega))
        (fun t ht => fin_ne_of_lt (by rw [out2_val ht]; simp only [wf, wireF_w, base_raw]; omega)),
        hq1_other _ (fin_ne_of_lt (by rw [out0_val hL]; simp only [wf, wireF_w, base_raw]; omega)), hin.wireF]
    have h2a : q2 (regA_w r L j) = a.testBit j := by
      rw [hq2_non _ (fun t ht => fin_ne_of_lt (by rw [regA_val hj, out1_val ht]; simp only [base_raw]; omega))
        (fun t ht => fin_ne_of_lt (by rw [regA_val hj, out2_val ht]; simp only [base_raw]; omega)),
        hq1_other _ (fin_ne_of_lt (by rw [regA_val hj, out0_val hL]; simp only [base_raw]; omega)), hin.regA j hj]
    rw [h2o, h2w, h2a]; cases flag <;> simp
  · intro z hz
    rw [hq5_non_all _ (fun t ht => (fin_ne_of_lt (by rw [out1_val ht]; omega)).symm)
      (fun t ht => (fin_ne_of_lt (by rw [out2_val ht]; omega)).symm)
      (fun t ht => (fin_ne_of_lt (by rw [out3_val ht]; omega)).symm)
      (fun t ht => (fin_ne_of_lt (by rw [out4_val ht]; omega)).symm)
      (fin_ne_of_lt (by rw [out0_val hL]; omega)).symm]
    exact hq_base z (by omega)
  · intro z hz hw0 hwW hwf hA hB hH
    rw [hq5_non_all _ (fun t ht => fin_ne_of_lt (by rw [out1_val ht]; omega))
      (fun t ht => fin_ne_of_lt (by rw [out2_val ht]; omega))
      (fun t ht => fin_ne_of_lt (by rw [out3_val ht]; omega))
      (fun t ht => fin_ne_of_lt (by rw [out4_val ht]; omega))
      (fin_ne_of_lt (by rw [out0_val hL]; omega))]
    exact hin.rest z hw0 hwW hwf hA hB hH

lemma nat_sub_add_mod {M a b : ℕ} (ha : a < M) (hb : b < M) :
    (M + (a + b) % M - a) % M = b := by
  by_cases hab : a + b < M
  · rw [Nat.mod_eq_of_lt hab, show M + (a + b) - a = b + M by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hb]
  · have hle : M ≤ a + b := by omega
    have hlt : a + b - M < M := by omega
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt, show M + (a + b - M) - a = b by omega,
      Nat.mod_eq_of_lt hb]

lemma nat_sub_sub_mod {M a h_val : ℕ} (ha : a < M) (hh : h_val < M) :
    (M + a - (M + a - h_val) % M) % M = h_val := by
  by_cases hle : h_val ≤ a
  · have hlt : a - h_val < M := by omega
    rw [show M + a - h_val = (a - h_val) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hlt,
      show M + a - (a - h_val) = h_val + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hh]
  · have hlt : M + a - h_val < M := by omega
    rw [Nat.mod_eq_of_lt hlt, show M + a - (M + a - h_val) = h_val by omega, Nat.mod_eq_of_lt hh]

lemma zmod_val_sub {M : ℕ} (hM : 1 ≤ M) (α β : ZMod M) :
    (α - β).val = (M + α.val - β.val) % M := by
  have : NeZero M := ⟨by omega⟩
  have hα : α.val < M := ZMod.val_lt α
  have hβ : β.val < M := ZMod.val_lt β
  have hcast : ((M + α.val - β.val : ℕ) : ZMod M) = α - β := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, zero_add,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [← hcast, ZMod.val_natCast]

lemma fbOutUnc_spec (r M L a b h_val : ℕ) (flag : Bool)
    (hr : 1 ≤ r) (hL : 1 ≤ L) (hM1 : 1 ≤ M) (hML : M < 2 ^ L)
    (ha : a < M) (hb : b < M) (hh : h_val < M) (hflag0 : flag = false → h_val = 0)
    (q : Qubits (fbOutW_raw r L))
    (hmid : FBMid r M L a b h_val flag q) :
    let q' := evalRevList (fbOutUnc r M L hr hL) q
    (∀ j < L, q' (out0_w r L j) = q (out0_w r L j)) ∧
      (∀ j < L, q' (out1_w r L j) = q (out1_w r L j)) ∧
      (∀ j < L, q' (out2_w r L j) = q (out2_w r L j)) ∧
      (∀ j < L, q' (out3_w r L j) = q (out3_w r L j)) ∧
      (∀ j < L, q' (out4_w r L j) = q (out4_w r L j)) ∧
      (∀ z : Fin (fbOutW_raw r L), z.val < base_raw r L → q' z = false) ∧
      (∀ z : Fin (fbOutW_raw r L), base_raw r L + 5 * L ≤ z.val → q' z = false) := by
  have hW : 2 * L ≤ (r + 1) * L := two_L_le_W r L hr
  let wf := wireF_w r L
  let o0 := out0_w r L 0
  let c6a := ccxLoop o0 (out4_w r L) (regA_w r L) L
      (fun j hj => fin_ne_of_lt (by rw [out0_val hL, out4_val hj]; omega))
      (fun j hj => (fin_ne_of_lt (by rw [regA_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
      (fun j hj => (fin_ne_of_lt (by rw [regA_val hj, out4_val hj]; simp only [base_raw]; omega)).symm)
  let c6b := ccxLoop o0 (out1_w r L) (regA_w r L) L
      (fun j hj => fin_ne_of_lt (by rw [out0_val hL, out1_val hj]; omega))
      (fun j hj => (fin_ne_of_lt (by rw [regA_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
      (fun j hj => (fin_ne_of_lt (by rw [regA_val hj, out1_val hj]; simp only [base_raw]; omega)).symm)
  let q6_1 := evalRevList c6a q
  let q6_2 := evalRev (.x o0) q6_1
  let q6_3 := evalRevList c6b q6_2
  let q6 := evalRev (.x o0) q6_3
  have hc6a := ccxLoop_spec o0 (out4_w r L) (regA_w r L) L
    (fun j hj => fin_ne_of_lt (by rw [out0_val hL, out4_val hj]; omega))
    (fun j hj => (fin_ne_of_lt (by rw [regA_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
    (fun i hi j hj => (fin_ne_of_lt (by rw [regA_val hj, out4_val hi]; simp only [base_raw]; omega)).symm)
    (fun _ hi _ hj => regA_inj hi hj) q
  have hc6b := ccxLoop_spec o0 (out1_w r L) (regA_w r L) L
    (fun j hj => fin_ne_of_lt (by rw [out0_val hL, out1_val hj]; omega))
    (fun j hj => (fin_ne_of_lt (by rw [regA_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
    (fun i hi j hj => (fin_ne_of_lt (by rw [regA_val hj, out1_val hi]; simp only [base_raw]; omega)).symm)
    (fun _ hi _ hj => regA_inj hi hj) q6_2
  have hq6_non : ∀ z, (∀ j < L, z ≠ regA_w r L j) → q6 z = q z := by
    intro z hz
    have h3z : q6_3 z = q6_2 z := hc6b.1 z hz
    have h1z : q6_1 z = q z := hc6a.1 z hz
    by_cases hzo : z = o0
    · rw [hzo]
      have h3o : q6_3 o0 = q6_2 o0 := hzo ▸ h3z
      have h1o : q6_1 o0 = q o0 := hzo ▸ h1z
      dsimp only [q6]; rw [evalRev_x, Function.update_self, h3o]
      dsimp only [q6_2]; rw [evalRev_x, Function.update_self, h1o, Bool.not_not]
    · dsimp only [q6]; rw [evalRev_x, Function.update_of_ne hzo, h3z]
      dsimp only [q6_2]; rw [evalRev_x, Function.update_of_ne hzo, h1z]
  have hq6_regA : ∀ j < L, q6 (regA_w r L j) = false := fun j hj => by
    have hne_ao : regA_w r L j ≠ o0 := fin_ne_of_lt (by rw [regA_val hj, out0_val hL]; simp only [base_raw]; omega)
    dsimp only [q6]; rw [evalRev_x, Function.update_of_ne hne_ao]
    dsimp only [q6_3]; rw [hc6b.2 j hj]
    have h2a : q6_2 (regA_w r L j) = q6_1 (regA_w r L j) := by
      dsimp only [q6_2]; rw [evalRev_x, Function.update_of_ne hne_ao]
    have h2o : q6_2 o0 = !flag := by
      have h1o : q6_1 o0 = flag := by
        rw [show q6_1 o0 = q o0 from hc6a.1 _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, out0_val hL]; simp only [base_raw]; omega)).symm),
          hmid.out0_0]
      dsimp only [q6_2]; rw [evalRev_x, Function.update_self, h1o]
    have h2o1 : q6_2 (out1_w r L j) = q (out1_w r L j) := by
      have hne_1o : out1_w r L j ≠ o0 := (fin_ne_of_lt (by rw [out0_val hL, out1_val hj]; omega)).symm
      dsimp only [q6_2]; rw [evalRev_x, Function.update_of_ne hne_1o]
      exact hc6a.1 _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, out1_val hj]; simp only [base_raw]; omega)).symm)
    have h1a : q6_1 (regA_w r L j) = xor (a.testBit j) (flag && q (out4_w r L j)) := by
      dsimp only [q6_1]; rw [hc6a.2 j hj, hmid.regA j hj, hmid.out0_0]
    rw [h2a, h1a, h2o, h2o1, hmid.out4 j hj, hmid.out1 j hj]
    cases flag <;> simp
  have hq6_scr : ∀ z, InScratch r L z → q6 z = false := fun z hz => by
    rw [hq6_non z (fun t ht => (fin_ne_of_lt (by rw [regA_val ht]; simp only [InScratch] at hz; simp only [base_raw] at hz ⊢; omega)).symm),
      hmid.high z (by simp only [InScratch] at hz; omega)]
  have hq6_tmp : ∀ j < L, q6 (tmp_w r L j) = false := fun j hj => by
    rw [hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, tmp_val hj]; simp only [base_raw]; omega)).symm),
      hmid.high _ (by rw [tmp_val hj]; omega)]
  have hq6_zA : q6 (zA_w r L) = false := by
    rw [hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht]; simp only [zA_w, base_raw]; omega)).symm),
      hmid.high _ (by simp only [zA_w]; omega)]
  have hq6_zB : q6 (zB_w r L) = false := by
    rw [hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht]; simp only [zB_w, base_raw]; omega)).symm),
      hmid.high _ (by simp only [zB_w]; omega)]
  have hq6_out1 : ∀ j < L, q6 (out1_w r L j) = if flag then ((a + b) % M).testBit j else a.testBit j := fun j hj => by
    rw [hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, out1_val hj]; simp only [base_raw]; omega)).symm),
      hmid.out1 j hj]
  have hq6_out4 : ∀ j < L, q6 (out4_w r L j) = if flag then a.testBit j else false := fun j hj => by
    rw [hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, out4_val hj]; simp only [base_raw]; omega)).symm),
      hmid.out4 j hj]
  have hML' : M < 2 ^ (L + 1) := lt_trans hML (by rw [pow_succ]; omega)
  let pre7 := subModM M (liftReg L (out1_w r L) (zA_w r L)) (liftReg L (out4_w r L) (zB_w r L))
      (tmp_w r L) (hIO_14 r L)
  have hout1_lt : (if flag then (a + b) % M else a) < M := by
    cases flag <;> simp [ha, Nat.mod_lt _ hM1]
  have hout4_lt : (if flag then a else 0) < M := by
    cases flag
    · simp; omega
    · simp [ha]
  have hout1_val : regVal q6 (liftReg L (out1_w r L) (zA_w r L)) (L + 1) =
      if flag then (a + b) % M else a := by
    rw [regVal_liftReg L _ _ q6 hq6_zA]
    apply regVal_eq_of_testBit (lt_trans hout1_lt hML)
    intro j hj; rw [hq6_out1 j hj]; cases flag <;> simp
  have hout4_val : regVal q6 (liftReg L (out4_w r L) (zB_w r L)) (L + 1) =
      if flag then a else 0 := by
    rw [regVal_liftReg L _ _ q6 hq6_zB]
    apply regVal_eq_of_testBit (lt_trans hout4_lt hML)
    intro j hj; rw [hq6_out4 j hj]; cases flag <;> simp
  have hsub7 := subModM_spec M hM1 hML _ _ (tmp_w r L) (hIO_14 r L) q6 hq6_scr hq6_tmp
    (by rw [hout1_val]; exact hout1_lt) (by rw [hout4_val]; exact hout4_lt)
  have hpre7_av : ∀ g ∈ pre7, gateAvoids (fun z => ∃ j < L, z = regB_w r L j) g := by
    apply subModM_avoid
    · intro i hi ⟨j, hj, heq⟩; dsimp only [liftReg] at heq; split_ifs at heq with h1
      · exact (fin_ne_of_lt (by rw [regB_val hj, out1_val h1]; simp only [base_raw]; omega)).symm heq
      · exact (fin_ne_of_lt (by rw [regB_val hj]; simp only [zA_w, base_raw]; omega)).symm heq
    · intro i hi ⟨j, hj, heq⟩; dsimp only [liftReg] at heq; split_ifs at heq with h1
      · exact (fin_ne_of_lt (by rw [regB_val hj, out4_val h1]; simp only [base_raw]; omega)).symm heq
      · exact (fin_ne_of_lt (by rw [regB_val hj]; simp only [zB_w, base_raw]; omega)).symm heq
    · intro i hi ⟨j, hj, heq⟩
      exact (fin_ne_of_lt (by rw [regB_val hj, tmp_val hi]; simp only [base_raw]; omega)).symm heq
    · rintro z hz ⟨j, hj, heq⟩; simp only [InScratch] at hz; rw [heq, regB_val hj] at hz; simp only [base_raw] at hz; omega
  have hccu7 := fbOutCCU_spec L pre7 o0 (tmp_w r L) (regB_w r L)
    (fun j hj => fin_ne_of_lt (by rw [out0_val hL, tmp_val hj]; omega))
    (fun j hj => (fin_ne_of_lt (by rw [regB_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
    (fun i hi j hj => (fin_ne_of_lt (by rw [regB_val hj, tmp_val hi]; simp only [base_raw]; omega)).symm)
    (fun _ hi _ hj => regB_inj hi hj) hpre7_av q6
    (hsub7.1 o0 (fun j hj => fin_ne_of_lt (by rw [out0_val hL, tmp_val hj]; omega)))
    (fun j hj => hsub7.1 (regB_w r L j) (fun t ht => fin_ne_of_lt (by rw [regB_val hj, tmp_val ht]; simp only [base_raw]; omega)))
  let q7 := evalRevList (fbOutCCU L pre7 o0 (tmp_w r L) (regB_w r L)
    (fun j hj => fin_ne_of_lt (by rw [out0_val hL, tmp_val hj]; omega))
    (fun j hj => (fin_ne_of_lt (by rw [regB_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
    (fun j hj => (fin_ne_of_lt (by rw [regB_val hj, tmp_val hj]; simp only [base_raw]; omega)).symm)) q6
  have hq7_non : ∀ z, (∀ j < L, z ≠ regB_w r L j) → q7 z = q6 z := hccu7.1
  have hq7_regB : ∀ j < L, q7 (regB_w r L j) = if flag then false else b.testBit j := fun j hj => by
    dsimp only [q7]
    rw [hccu7.2 j hj]
    have h6o0 : q6 o0 = flag := by
      rw [hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, out0_val hL]; simp only [base_raw]; omega)).symm),
        hmid.out0_0]
    have h6b : q6 (regB_w r L j) = b.testBit j := by
      rw [hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, regB_val hj]; omega)).symm),
        hmid.regB j hj]
    have h7t := hsub7.2.2 j hj
    rw [hout1_val, hout4_val] at h7t
    rw [h6o0, h6b, h7t]
    cases flag
    · simp
    · simp [nat_sub_add_mod ha hb]
  let c8 := ccxLoop o0 (out2_w r L) (regB_w r L) L
      (fun j hj => fin_ne_of_lt (by rw [out0_val hL, out2_val hj]; omega))
      (fun j hj => (fin_ne_of_lt (by rw [regB_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
      (fun j hj => (fin_ne_of_lt (by rw [regB_val hj, out2_val hj]; simp only [base_raw]; omega)).symm)
  let q8_0 := evalRev (.x o0) q7
  let q8_1 := evalRevList c8 q8_0
  let q8 := evalRev (.x o0) q8_1
  have hc8 := ccxLoop_spec o0 (out2_w r L) (regB_w r L) L
    (fun j hj => fin_ne_of_lt (by rw [out0_val hL, out2_val hj]; omega))
    (fun j hj => (fin_ne_of_lt (by rw [regB_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
    (fun i hi j hj => (fin_ne_of_lt (by rw [regB_val hj, out2_val hi]; simp only [base_raw]; omega)).symm)
    (fun _ hi _ hj => regB_inj hi hj) q8_0
  have hq8_non : ∀ z, (∀ j < L, z ≠ regB_w r L j) → q8 z = q7 z := by
    intro z hz
    have h1z : q8_1 z = q8_0 z := hc8.1 z hz
    by_cases hzo : z = o0
    · rw [hzo]
      have h1o : q8_1 o0 = q8_0 o0 := hzo ▸ h1z
      dsimp only [q8]; rw [evalRev_x, Function.update_self, h1o]
      dsimp only [q8_0]; rw [evalRev_x, Function.update_self, Bool.not_not]
    · dsimp only [q8]; rw [evalRev_x, Function.update_of_ne hzo, h1z]
      dsimp only [q8_0]; rw [evalRev_x, Function.update_of_ne hzo]
  have hq8_regB : ∀ j < L, q8 (regB_w r L j) = false := fun j hj => by
    have hne_bo : regB_w r L j ≠ o0 := fin_ne_of_lt (by rw [regB_val hj, out0_val hL]; simp only [base_raw]; omega)
    dsimp only [q8]; rw [evalRev_x, Function.update_of_ne hne_bo]
    dsimp only [q8_1]; rw [hc8.2 j hj]
    have h80b : q8_0 (regB_w r L j) = q7 (regB_w r L j) := by
      dsimp only [q8_0]; rw [evalRev_x, Function.update_of_ne hne_bo]
    have h80o : q8_0 o0 = !flag := by
      have h7o : q7 o0 = flag := by
        rw [hq7_non _ (fun t ht => (fin_ne_of_lt (by rw [regB_val ht, out0_val hL]; simp only [base_raw]; omega)).symm),
          hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, out0_val hL]; simp only [base_raw]; omega)).symm),
          hmid.out0_0]
      dsimp only [q8_0]; rw [evalRev_x, Function.update_self, h7o]
    have h80o2 : q8_0 (out2_w r L j) = q (out2_w r L j) := by
      have hne_2o : out2_w r L j ≠ o0 := (fin_ne_of_lt (by rw [out0_val hL, out2_val hj]; omega)).symm
      dsimp only [q8_0]; rw [evalRev_x, Function.update_of_ne hne_2o]
      rw [hq7_non _ (fun t ht => (fin_ne_of_lt (by rw [regB_val ht, out2_val hj]; simp only [base_raw]; omega)).symm),
        hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, out2_val hj]; simp only [base_raw]; omega)).symm)]
    rw [h80b, h80o, h80o2, hq7_regB j hj, hmid.out2 j hj]
    cases flag <;> simp
  have hq8_to_q6 : ∀ z, (∀ j < L, z ≠ regB_w r L j) → q8 z = q6 z := by
    intro z hz; rw [hq8_non z hz, hq7_non z hz]
  have hq8_scr : ∀ z, InScratch r L z → q8 z = false := fun z hz => by
    rw [hq8_to_q6 z (fun t ht => (fin_ne_of_lt (by rw [regB_val ht]; simp only [InScratch] at hz; simp only [base_raw] at hz ⊢; omega)).symm),
      hq6_scr z hz]
  have hq8_tmp : ∀ j < L, q8 (tmp_w r L j) = false := fun j hj => by
    rw [hq8_to_q6 _ (fun t ht => (fin_ne_of_lt (by rw [regB_val ht, tmp_val hj]; simp only [base_raw]; omega)).symm),
      hq6_tmp j hj]
  have hq8_zA : q8 (zA_w r L) = false := by
    rw [hq8_to_q6 _ (fun t ht => (fin_ne_of_lt (by rw [regB_val ht]; simp only [zA_w, base_raw]; omega)).symm),
      hq6_zA]
  have hq8_zB : q8 (zB_w r L) = false := by
    rw [hq8_to_q6 _ (fun t ht => (fin_ne_of_lt (by rw [regB_val ht]; simp only [zB_w, base_raw]; omega)).symm),
      hq6_zB]
  have hq8_out3 : ∀ j < L, q8 (out3_w r L j) = q (out3_w r L j) := fun j hj => by
    rw [hq8_to_q6 _ (fun t ht => (fin_ne_of_lt (by rw [regB_val ht, out3_val hj]; simp only [base_raw]; omega)).symm),
      hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, out3_val hj]; simp only [base_raw]; omega)).symm)]
  have hq8_out4 : ∀ j < L, q8 (out4_w r L j) = q (out4_w r L j) := fun j hj => by
    rw [hq8_to_q6 _ (fun t ht => (fin_ne_of_lt (by rw [regB_val ht, out4_val hj]; simp only [base_raw]; omega)).symm),
      hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, out4_val hj]; simp only [base_raw]; omega)).symm)]
  let pre9 := subModM M (liftReg L (out4_w r L) (zA_w r L)) (liftReg L (out3_w r L) (zB_w r L))
      (tmp_w r L) (hIO_43 r L)
  have hout3_lt : (if flag then (M + a - h_val) % M else 0) < M := by
    cases flag
    · exact hM1
    · exact Nat.mod_lt _ hM1
  have hout4_val8 : regVal q8 (liftReg L (out4_w r L) (zA_w r L)) (L + 1) =
      if flag then a else 0 := by
    rw [regVal_liftReg L _ _ q8 hq8_zA]
    apply regVal_eq_of_testBit (lt_trans hout4_lt hML)
    intro j hj; rw [hq8_out4 j hj, hmid.out4 j hj]; cases flag <;> simp
  have hout3_val8 : regVal q8 (liftReg L (out3_w r L) (zB_w r L)) (L + 1) =
      if flag then (M + a - h_val) % M else 0 := by
    rw [regVal_liftReg L _ _ q8 hq8_zB]
    apply regVal_eq_of_testBit (lt_trans hout3_lt hML)
    intro j hj; rw [hq8_out3 j hj, hmid.out3 j hj]; cases flag <;> simp
  have hsub9 := subModM_spec M hM1 hML _ _ (tmp_w r L) (hIO_43 r L) q8 hq8_scr hq8_tmp
    (by rw [hout4_val8]; exact hout4_lt) (by rw [hout3_val8]; exact hout3_lt)
  have hpre9_av : ∀ g ∈ pre9, gateAvoids (fun z => ∃ j < L, z = regH_w r L j) g := by
    apply subModM_avoid
    · intro i hi ⟨j, hj, heq⟩; dsimp only [liftReg] at heq; split_ifs at heq with h1
      · exact (fin_ne_of_lt (by rw [regH_val hj, out4_val h1]; simp only [base_raw]; omega)).symm heq
      · exact (fin_ne_of_lt (by rw [regH_val hj]; simp only [zA_w, base_raw]; omega)).symm heq
    · intro i hi ⟨j, hj, heq⟩; dsimp only [liftReg] at heq; split_ifs at heq with h1
      · exact (fin_ne_of_lt (by rw [regH_val hj, out3_val h1]; simp only [base_raw]; omega)).symm heq
      · exact (fin_ne_of_lt (by rw [regH_val hj]; simp only [zB_w, base_raw]; omega)).symm heq
    · intro i hi ⟨j, hj, heq⟩
      exact (fin_ne_of_lt (by rw [regH_val hj, tmp_val hi]; simp only [base_raw]; omega)).symm heq
    · rintro z hz ⟨j, hj, heq⟩; simp only [InScratch] at hz; rw [heq, regH_val hj] at hz; simp only [base_raw] at hz; omega
  have hccu9 := fbOutCCU_spec L pre9 o0 (tmp_w r L) (regH_w r L)
    (fun j hj => fin_ne_of_lt (by rw [out0_val hL, tmp_val hj]; omega))
    (fun j hj => (fin_ne_of_lt (by rw [regH_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
    (fun i hi j hj => (fin_ne_of_lt (by rw [regH_val hj, tmp_val hi]; simp only [base_raw]; omega)).symm)
    (fun _ hi _ hj => regH_inj hi hj) hpre9_av q8
    (hsub9.1 o0 (fun j hj => fin_ne_of_lt (by rw [out0_val hL, tmp_val hj]; omega)))
    (fun j hj => hsub9.1 (regH_w r L j) (fun t ht => fin_ne_of_lt (by rw [regH_val hj, tmp_val ht]; simp only [base_raw]; omega)))
  let q9 := evalRevList (fbOutCCU L pre9 o0 (tmp_w r L) (regH_w r L)
    (fun j hj => fin_ne_of_lt (by rw [out0_val hL, tmp_val hj]; omega))
    (fun j hj => (fin_ne_of_lt (by rw [regH_val hj, out0_val hL]; simp only [base_raw]; omega)).symm)
    (fun j hj => (fin_ne_of_lt (by rw [regH_val hj, tmp_val hj]; simp only [base_raw]; omega)).symm)) q8
  have hq9_non : ∀ z, (∀ j < L, z ≠ regH_w r L j) → q9 z = q8 z := hccu9.1
  have hq9_regH : ∀ j < L, q9 (regH_w r L j) = false := fun j hj => by
    dsimp only [q9]
    rw [hccu9.2 j hj]
    have h8o0 : q8 o0 = flag := by
      rw [hq8_to_q6 _ (fun t ht => (fin_ne_of_lt (by rw [regB_val ht, out0_val hL]; simp only [base_raw]; omega)).symm),
        hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, out0_val hL]; simp only [base_raw]; omega)).symm),
        hmid.out0_0]
    have h8h : q8 (regH_w r L j) = h_val.testBit j := by
      rw [hq8_to_q6 _ (fun t ht => (fin_ne_of_lt (by rw [regB_val ht, regH_val hj]; omega)).symm),
        hq6_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, regH_val hj]; omega)).symm),
        hmid.regH j hj]
    have h9t := hsub9.2.2 j hj
    rw [hout4_val8, hout3_val8] at h9t
    rw [h8o0, h8h, h9t]
    cases hfl : flag
    · simp [hflag0 hfl]
    · simp [nat_sub_sub_mod ha hh]
  let q10_0 := evalRev (.cnot o0 wf (fin_ne_of_lt (by rw [out0_val hL]; simp only [wf, wireF_w, base_raw]; omega)).symm) q9
  let q10_1 := evalRev (.x (w0_w r L)) q10_0
  let q10 := evalRev (.x (wW_w r L)) q10_1
  have hq_unc : evalRevList (fbOutUnc r M L hr hL) q = q10 := by
    simp only [fbOutUnc, evalRevList_append, evalRevList_cons, evalRevList_nil]
    rfl
  have hq9_all_non : ∀ z, (∀ j < L, z ≠ regA_w r L j) → (∀ j < L, z ≠ regB_w r L j) →
      (∀ j < L, z ≠ regH_w r L j) → q9 z = q z := fun z hA hB hH => by
    rw [hq9_non z hH, hq8_non z hB, hq7_non z hB, hq6_non z hA]
  have hq10_non : ∀ z, z ≠ wf → z ≠ w0_w r L → z ≠ wW_w r L → q10 z = q9 z := fun z h1 h2 h3 => by
    simp only [q10, q10_1, q10_0, evalRev_x, evalRev_cnot]
    rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  have hq10_out : ∀ z : Fin (fbOutW_raw r L), base_raw r L ≤ z.val → q10 z = q z := by
    intro z hz
    rw [hq10_non z (fin_ne_of_lt (by simp only [wf, wireF_w, base_raw] at hz ⊢; omega)).symm
      (fin_ne_of_lt (by simp only [w0_w, base_raw] at hz ⊢; omega)).symm
      (fin_ne_of_lt (by simp only [wW_w, base_raw] at hz ⊢; omega)).symm]
    apply hq9_all_non
    · intro t ht; exact (fin_ne_of_lt (by rw [regA_val ht]; simp only [base_raw] at hz ⊢; omega)).symm
    · intro t ht; exact (fin_ne_of_lt (by rw [regB_val ht]; simp only [base_raw] at hz ⊢; omega)).symm
    · intro t ht; exact (fin_ne_of_lt (by rw [regH_val ht]; simp only [base_raw] at hz ⊢; omega)).symm
  rw [hq_unc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; exact hq10_out _ (by rw [out0_val hj]; omega)
  · intro j hj; exact hq10_out _ (by rw [out1_val hj]; omega)
  · intro j hj; exact hq10_out _ (by rw [out2_val hj]; omega)
  · intro j hj; exact hq10_out _ (by rw [out3_val hj]; omega)
  · intro j hj; exact hq10_out _ (by rw [out4_val hj]; omega)
  · intro z hz
    by_cases hzwW : z = wW_w r L
    · rw [hzwW]
      have hne1 : wW_w r L ≠ w0_w r L := (fin_ne_of_lt (by simp only [wW_w, w0_w]; omega)).symm
      have hne2 : wW_w r L ≠ wf := fin_ne_of_lt (by simp only [wW_w, wf, wireF_w]; omega)
      have h9wW : q9 (wW_w r L) = true := by
        rw [hq9_all_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht]; simp only [wW_w]; omega)).symm)
          (fun t ht => fin_ne_of_lt (by rw [regB_val ht]; simp only [wW_w]; omega))
          (fun t ht => fin_ne_of_lt (by rw [regH_val ht]; simp only [wW_w]; omega)), hmid.wW]
      simp [q10, q10_1, q10_0, hne1, hne2, h9wW]
    · by_cases hzw0 : z = w0_w r L
      · rw [hzw0]
        have hne1 : w0_w r L ≠ wW_w r L := fin_ne_of_lt (by simp only [w0_w, wW_w]; omega)
        have hne2 : w0_w r L ≠ wf := fin_ne_of_lt (by simp only [w0_w, wf, wireF_w]; omega)
        have h9w0 : q9 (w0_w r L) = true := by
          rw [hq9_all_non _ (fun t ht => fin_ne_of_lt (by rw [regA_val ht]; simp only [w0_w]; omega))
            (fun t ht => fin_ne_of_lt (by rw [regB_val ht]; simp only [w0_w]; omega))
            (fun t ht => fin_ne_of_lt (by rw [regH_val ht]; simp only [w0_w]; omega)), hmid.w0]
        simp [q10, q10_1, q10_0, hne1, hne2, h9w0]
      · by_cases hzwf : z = wf
        · rw [hzwf]
          have hne1 : wf ≠ wW_w r L := (fin_ne_of_lt (by simp only [wW_w, wf, wireF_w]; omega)).symm
          have hne2 : wf ≠ w0_w r L := (fin_ne_of_lt (by simp only [w0_w, wf, wireF_w]; omega)).symm
          have h9wf : q9 wf = flag := by
            rw [hq9_all_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht]; simp only [wf, wireF_w]; omega)).symm)
              (fun t ht => (fin_ne_of_lt (by rw [regB_val ht]; simp only [wf, wireF_w]; omega)).symm)
              (fun t ht => fin_ne_of_lt (by rw [regH_val ht]; simp only [wf, wireF_w]; omega)), hmid.wireF]
          have h9o0 : q9 o0 = flag := by
            rw [hq9_all_non _ (fun t ht => (fin_ne_of_lt (by rw [regA_val ht, out0_val hL]; simp only [base_raw]; omega)).symm)
              (fun t ht => (fin_ne_of_lt (by rw [regB_val ht, out0_val hL]; simp only [base_raw]; omega)).symm)
              (fun t ht => (fin_ne_of_lt (by rw [regH_val ht, out0_val hL]; simp only [base_raw]; omega)).symm),
              hmid.out0_0]
          simp [q10, q10_1, q10_0, hne1, hne2, h9wf, h9o0]
        · rw [hq10_non z hzwf hzw0 hzwW]
          by_cases hA : ∃ j < L, z = regA_w r L j
          · obtain ⟨j, hj, rfl⟩ := hA
            rw [hq9_non _ (fun t ht => fin_ne_of_lt (by rw [regA_val hj, regH_val ht]; omega)),
              hq8_non _ (fun t ht => fin_ne_of_lt (by rw [regA_val hj, regB_val ht]; omega)),
              hq7_non _ (fun t ht => fin_ne_of_lt (by rw [regA_val hj, regB_val ht]; omega)),
              hq6_regA j hj]
          · have hA' : ∀ j < L, z ≠ regA_w r L j := fun j hj heq => hA ⟨j, hj, heq⟩
            by_cases hB : ∃ j < L, z = regB_w r L j
            · obtain ⟨j, hj, rfl⟩ := hB
              rw [hq9_non _ (fun t ht => fin_ne_of_lt (by rw [regB_val hj, regH_val ht]; omega)),
                hq8_regB j hj]
            · have hB' : ∀ j < L, z ≠ regB_w r L j := fun j hj heq => hB ⟨j, hj, heq⟩
              by_cases hH : ∃ j < L, z = regH_w r L j
              · obtain ⟨j, hj, rfl⟩ := hH
                exact hq9_regH j hj
              · have hH' : ∀ j < L, z ≠ regH_w r L j := fun j hj heq => hH ⟨j, hj, heq⟩
                rw [hq9_all_non z hA' hB' hH']
                exact hmid.low_rest z hz hzw0 hzwW hzwf hA' hB' hH'
  · intro z hz
    rw [hq10_out z (by omega), hmid.high z hz]

lemma fbOutSwap_spec (r L : ℕ) (hr : 1 ≤ r) (q : Qubits (fbOutW_raw r L))
    (hq_low : ∀ z : Fin (fbOutW_raw r L), z.val < base_raw r L → q z = false)
    (hq_high : ∀ z : Fin (fbOutW_raw r L), base_raw r L + 5 * L ≤ z.val → q z = false) :
    let q' := evalRevList (fbOutSwap r L hr) q
    (∀ j : ℕ, (hj : j < 5 * L) →
      q' ⟨j, by simp only [fbOutW_raw]; have := five_L_le_three_W r L hr; omega⟩ =
        q (outAll_w r L j)) ∧
      (∀ z : Fin (fbOutW_raw r L), 5 * L ≤ z.val → q' z = false) := by
  have h5 : 5 * L ≤ 3 * ((r + 1) * L) := five_L_le_three_W r L hr
  have hs := swapLoop_spec (outAll_w r L) (lowAll_w r L) (5 * L)
    (fun i hi j hj heq => by have := congrArg Fin.val heq; rw [outAll_val hi, outAll_val hj] at this; omega)
    (fun i hi j hj heq => by have := congrArg Fin.val heq; rw [lowAll_val hi, lowAll_val hj] at this; omega)
    (fun i hi j hj => (fin_ne_of_lt (by rw [lowAll_val hj, outAll_val hi]; simp only [base_raw]; omega)).symm) q
  change (∀ z : Fin (fbOutW_raw r L), (∀ j < 5 * L, z ≠ outAll_w r L j ∧ z ≠ lowAll_w r L j) →
      evalRevList (fbOutSwap r L hr) q z = q z) ∧
    (∀ j < 5 * L, evalRevList (fbOutSwap r L hr) q (outAll_w r L j) = q (lowAll_w r L j) ∧
      evalRevList (fbOutSwap r L hr) q (lowAll_w r L j) = q (outAll_w r L j)) at hs
  refine ⟨?_, ?_⟩
  · intro j hj
    have hlow : (⟨j, by simp only [fbOutW_raw]; omega⟩ : Fin (fbOutW_raw r L)) = lowAll_w r L j := by
      ext; rw [lowAll_val hj]
    rw [hlow]
    exact (hs.2 j hj).2
  · intro z hz
    by_cases hlt1 : z.val < base_raw r L
    · rw [hs.1 z (fun j hj => ⟨(fin_ne_of_lt (by rw [outAll_val hj]; omega)),
        (fin_ne_of_lt (by rw [lowAll_val hj]; omega)).symm⟩)]
      exact hq_low z hlt1
    · by_cases hlt2 : z.val < base_raw r L + 5 * L
      · set t := z.val - base_raw r L
        have ht : t < 5 * L := by omega
        have hz_eq : z = outAll_w r L t := by ext; rw [outAll_val ht]; omega
        rw [hz_eq, (hs.2 t ht).1]
        exact hq_low _ (by rw [lowAll_val ht]; simp only [base_raw]; omega)
      · rw [hs.1 z (fun j hj => ⟨(fin_ne_of_lt (by rw [outAll_val hj]; omega)).symm,
          (fin_ne_of_lt (by rw [lowAll_val hj]; simp only [base_raw] at hlt1 ⊢; omega)).symm⟩)]
        exact hq_high z (by omega)

lemma qubits_append_lt {a b : ℕ} (u : Qubits a) (v : Qubits b) {i : ℕ} (hi : i < a) :
    Fin.append u v ⟨i, by omega⟩ = u ⟨i, hi⟩ := by
  dsimp only [Fin.append, Fin.addCases]
  rw [dif_pos hi]
  rfl

lemma qubits_append_ge {a b : ℕ} (u : Qubits a) (v : Qubits b) {i : ℕ} (ha : a ≤ i) (hi : i < a + b) :
    Fin.append u v ⟨i, hi⟩ = v ⟨i - a, by omega⟩ := by
  dsimp only [Fin.append, Fin.addCases]
  rw [dif_neg (by omega)]
  simp

lemma fd_q_ge_two (D : FieldData) : 2 ≤ D.q := by
  have h1 : 2 ^ 1 ≤ D.p ^ D.r := by
    calc 2 ^ 1 = 2 := by norm_num
      _ ≤ D.p := D.hp.two_le
      _ = D.p ^ 1 := (pow_one D.p).symm
      _ ≤ D.p ^ D.r := Nat.pow_le_pow_right D.hp.pos D.hr
  simpa [FieldData.q] using h1

lemma fd_two_le_labW (D : FieldData) : 2 ≤ D.labW := by
  by_contra hlt
  have hle : D.q ^ 2 ≤ 2 ^ D.labW := by
    unfold FieldData.labW
    exact Nat.le_pow_clog (by decide) (D.q ^ 2)
  have hpow : 2 ^ D.labW ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
  have hq := fd_q_ge_two D
  have hq4 : 4 ≤ D.q ^ 2 := by nlinarith
  omega

lemma fd_one_le_labW (D : FieldData) : 1 ≤ D.labW := by
  have := fd_two_le_labW D
  omega

lemma fd_m_lt_two_pow_labW (D : FieldData) : D.q - 1 < 2 ^ D.labW := by
  have hq := fd_q_ge_two D
  have hle1 : D.q ≤ D.q ^ 2 := by nlinarith
  have hle2 : D.q ^ 2 ≤ 2 ^ D.labW := by
    unfold FieldData.labW
    exact Nat.le_pow_clog (by decide) (D.q ^ 2)
  omega

lemma fd_digit_zero (D : FieldData) (j : ℕ) : D.digit 0 j = 0 := by
  simp [FieldData.digit]

lemma testBit_one (j : ℕ) : (1 : ℕ).testBit j = decide (j = 0) := by
  cases j with
  | zero => decide
  | succ k =>
    simp [Nat.testBit_eq_decide_div_mod_eq,
      Nat.div_eq_of_lt (by have := Nat.one_le_pow (k + 1) 2 (by decide); omega : 1 < 2 ^ (k + 1))]

lemma bMidCode_padTo_spec (D : FieldData) (p : D.Lab × D.Lab × Option D.Lab) :
    FBIn D.r D.labW p.1.val p.2.1.val (Option.elim p.2.2 0 ZMod.val) p.2.2.isSome
      (padTo (fbOutW_raw D.r D.labW) (bMidCode D p)) := by
  rcases p with ⟨α, β, η?⟩
  have hL2 : 2 ≤ D.labW := fd_two_le_labW D
  have hW : 2 * D.labW ≤ (D.r + 1) * D.labW := two_L_le_W D.r D.labW D.hr
  have h3W : (D.r + 1) * D.labW + (D.r + 1) * D.labW + (D.r + 1) * D.labW ≤ fbOutW_raw D.r D.labW := by
    simp only [fbOutW_raw]; omega
  have htag_inr : ∀ (d : D.Lab) (i : ℕ) (hi : i < (D.r + 1) * D.labW),
      D.tagCode (Sum.inr d) ⟨i, hi⟩ =
        if i = 0 then true else if D.labW ≤ i ∧ i < 2 * D.labW then d.val.testBit (i - D.labW) else false := by
    intro d i hi
    dsimp only [FieldData.tagCode, packNat]
    have hdiv_lt : i / D.labW < D.r + 1 := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hi)
    have hmod_lt : i % D.labW < D.labW := Nat.mod_lt i (by omega)
    by_cases h0 : i = 0
    · subst h0; simp
    · by_cases h1 : i < D.labW
      · have hdiv0 : i / D.labW = 0 := Nat.div_eq_of_lt h1
        have hmod : i % D.labW = i := Nat.mod_eq_of_lt h1
        simp only [hdiv0, ↓reduceIte, hmod, testBit_one, h0, decide_false,
          show ¬ (D.labW ≤ i ∧ i < 2 * D.labW) by omega]
      · by_cases h2 : i < 2 * D.labW
        · have hdiv1 : i / D.labW = 1 := by
            have := Nat.div_add_mod i D.labW
            have hle1 : 1 ≤ i / D.labW := Nat.div_pos (by omega) (by omega)
            have hlt2 : i / D.labW < 2 := Nat.div_lt_of_lt_mul (by omega)
            omega
          have hmod : i % D.labW = i - D.labW := by
            have := Nat.div_add_mod i D.labW; rw [hdiv1] at this; omega
          simp only [hdiv1, one_ne_zero, ↓reduceIte, hmod, h0,
            show D.labW ≤ i ∧ i < 2 * D.labW by omega, and_self]
        · have hdiv2 : 2 ≤ i / D.labW := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
          have hne0 : i / D.labW ≠ 0 := by omega
          have hne1 : i / D.labW ≠ 1 := by omega
          simp only [hne0, ↓reduceIte, hne1, Nat.zero_testBit, h0,
            show ¬ (D.labW ≤ i ∧ i < 2 * D.labW) by omega]
  have htag_none : ∀ (i : ℕ) (hi : i < (D.r + 1) * D.labW), D.tagCode (D.xEmb none) ⟨i, hi⟩ = false := by
    intro i hi
    simp only [FieldData.xEmb, FieldData.tagCode, packNat, fd_digit_zero]
    split_ifs <;> simp
  have hbm_lt1 : ∀ (i : ℕ) (hi : i < (D.r + 1) * D.labW),
      bMidCode D (α, β, η?) ⟨i, by omega⟩ = D.tagCode (Sum.inr α) ⟨i, hi⟩ := fun i hi => by
    unfold bMidCode
    have h1 := qubits_append_lt (Fin.append (D.tagCode (Sum.inr α)) (D.tagCode (Sum.inr β)))
      (D.tagCode (D.xEmb η?)) (by omega : i < (D.r + 1) * D.labW + (D.r + 1) * D.labW)
    have h2 := qubits_append_lt (D.tagCode (Sum.inr α)) (D.tagCode (Sum.inr β)) hi
    exact h1.trans h2
  have hbm_lt2 : ∀ (i : ℕ) (h1 : (D.r + 1) * D.labW ≤ i) (hi : i < 2 * ((D.r + 1) * D.labW)),
      bMidCode D (α, β, η?) ⟨i, by omega⟩ = D.tagCode (Sum.inr β) ⟨i - (D.r + 1) * D.labW, by omega⟩ := fun i h1 hi => by
    unfold bMidCode
    have ha := qubits_append_lt (Fin.append (D.tagCode (Sum.inr α)) (D.tagCode (Sum.inr β)))
      (D.tagCode (D.xEmb η?)) (by omega : i < (D.r + 1) * D.labW + (D.r + 1) * D.labW)
    have hb := qubits_append_ge (D.tagCode (Sum.inr α)) (D.tagCode (Sum.inr β)) h1 (by omega : i < (D.r + 1) * D.labW + (D.r + 1) * D.labW)
    exact ha.trans hb
  have hbm_lt3 : ∀ (i : ℕ) (h1 : 2 * ((D.r + 1) * D.labW) ≤ i) (hi : i < 3 * ((D.r + 1) * D.labW)),
      bMidCode D (α, β, η?) ⟨i, by omega⟩ = D.tagCode (D.xEmb η?) ⟨i - 2 * ((D.r + 1) * D.labW), by omega⟩ := fun i h1 hi => by
    unfold bMidCode
    have ha := qubits_append_ge (Fin.append (D.tagCode (Sum.inr α)) (D.tagCode (Sum.inr β)))
      (D.tagCode (D.xEmb η?)) (by omega : (D.r + 1) * D.labW + (D.r + 1) * D.labW ≤ i)
      (by omega : i < (D.r + 1) * D.labW + (D.r + 1) * D.labW + (D.r + 1) * D.labW)
    rw [ha]
    congr 1; ext; simp; omega
  have hbm_pad : ∀ (z : Fin (fbOutW_raw D.r D.labW)),
      padTo (fbOutW_raw D.r D.labW) (bMidCode D (α, β, η?)) z =
        if hz : z.val < 3 * ((D.r + 1) * D.labW) then
          bMidCode D (α, β, η?) ⟨z.val, by omega⟩
        else false := fun z => by
    simp only [padTo]; split_ifs with h1 h2 <;> first | rfl | omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbm_pad, dif_pos (by simp only [w0_w]; omega)]
    rw [hbm_lt1 _ (by simp only [w0_w]; omega), htag_inr]
    simp [w0_w]
  · rw [hbm_pad, dif_pos (by simp only [wW_w]; omega)]
    rw [hbm_lt2 _ (by simp only [wW_w]; omega) (by simp only [wW_w]; omega), htag_inr]
    simp [wW_w]
  · rw [hbm_pad, dif_pos (by simp only [wireF_w]; omega)]
    rw [hbm_lt3 _ (by simp only [wireF_w]; omega) (by simp only [wireF_w]; omega)]
    cases η? with
    | none => simp [wireF_w, htag_none 0 (by omega)]
    | some η => simp [FieldData.xEmb, htag_inr, wireF_w]
  · intro j hj
    rw [hbm_pad, dif_pos (by rw [regA_val (r := D.r) hj]; omega)]
    rw [hbm_lt1 _ (by rw [regA_val (r := D.r) hj]; omega), htag_inr]
    have hval := regA_val (r := D.r) hj
    simp only [hval, show ¬ (D.labW + j = 0) by omega, ↓reduceIte,
      show D.labW ≤ D.labW + j ∧ D.labW + j < 2 * D.labW by omega, Nat.add_sub_cancel_left,
      and_self]
  · intro j hj
    rw [hbm_pad, dif_pos (by rw [regB_val (r := D.r) hj]; omega)]
    rw [hbm_lt2 _ (by rw [regB_val (r := D.r) hj]; omega) (by rw [regB_val (r := D.r) hj]; omega), htag_inr]
    have hval := regB_val (r := D.r) hj
    have hsub : (D.r + 1) * D.labW + D.labW + j - (D.r + 1) * D.labW = D.labW + j := by omega
    simp only [hval, hsub, show ¬ (D.labW + j = 0) by omega, ↓reduceIte,
      show D.labW ≤ D.labW + j ∧ D.labW + j < 2 * D.labW by omega, Nat.add_sub_cancel_left,
      and_self]
  · intro j hj
    rw [hbm_pad, dif_pos (by rw [regH_val (r := D.r) hj]; omega)]
    rw [hbm_lt3 _ (by rw [regH_val (r := D.r) hj]; omega) (by rw [regH_val (r := D.r) hj]; omega)]
    have hval := regH_val (r := D.r) hj
    have hsub : 2 * ((D.r + 1) * D.labW) + D.labW + j - 2 * ((D.r + 1) * D.labW) = D.labW + j := by omega
    cases η? with
    | none =>
      rw [htag_none _ (by omega)]
      simp
    | some η =>
      simp only [Option.elim_some, FieldData.xEmb, hval, hsub]
      rw [htag_inr]
      simp only [show ¬ (D.labW + j = 0) by omega, ↓reduceIte,
        show D.labW ≤ D.labW + j ∧ D.labW + j < 2 * D.labW by omega, Nat.add_sub_cancel_left,
        and_self]
  · intro z hw0 hwW hwf hA hB hH
    rw [hbm_pad]
    split_ifs with hz3
    · by_cases hz1 : z.val < (D.r + 1) * D.labW
      · rw [hbm_lt1 z.val hz1, htag_inr]
        by_cases h0 : z.val = 0
        · exact absurd (Fin.ext h0) hw0
        · rw [if_neg h0]
          by_cases hL1 : D.labW ≤ z.val ∧ z.val < 2 * D.labW
          · exfalso
            apply hA (z.val - D.labW) (by omega)
            ext; rw [regA_val (by omega)]; omega
          · rw [if_neg hL1]
      · by_cases hz2 : z.val < 2 * ((D.r + 1) * D.labW)
        · rw [hbm_lt2 z.val (by omega) hz2, htag_inr]
          by_cases h0 : z.val - (D.r + 1) * D.labW = 0
          · exfalso; apply hwW; ext; simp only [wW_w]; omega
          · rw [if_neg h0]
            by_cases hL1 : D.labW ≤ z.val - (D.r + 1) * D.labW ∧ z.val - (D.r + 1) * D.labW < 2 * D.labW
            · exfalso
              apply hB (z.val - (D.r + 1) * D.labW - D.labW) (by omega)
              ext; rw [regB_val (by omega)]; omega
            · rw [if_neg hL1]
        · rw [hbm_lt3 z.val (by omega) hz3]
          cases η? with
          | none => exact htag_none _ (by omega)
          | some η =>
            simp only [FieldData.xEmb]
            rw [htag_inr]
            by_cases h0 : z.val - 2 * ((D.r + 1) * D.labW) = 0
            · exfalso; apply hwf; ext; simp only [wireF_w]; omega
            · rw [if_neg h0]
              by_cases hL1 : D.labW ≤ z.val - 2 * ((D.r + 1) * D.labW) ∧
                  z.val - 2 * ((D.r + 1) * D.labW) < 2 * D.labW
              · exfalso
                apply hH (z.val - 2 * ((D.r + 1) * D.labW) - D.labW) (by omega)
                ext; rw [regH_val (by omega)]; omega
              · rw [if_neg hL1]
    · rfl

lemma fbOutRev_spec (r M L a b h_val : ℕ) (flag : Bool)
    (hr : 1 ≤ r) (hL : 1 ≤ L) (hM1 : 1 ≤ M) (hML : M < 2 ^ L)
    (ha : a < M) (hb : b < M) (hh : h_val < M) (hflag0 : flag = false → h_val = 0)
    (q : Qubits (fbOutW_raw r L))
    (hin : FBIn r L a b h_val flag q) :
    let q' := evalRevList (fbOutRev r M L hr hL) q
    (∀ (j : ℕ) (hj : j < L), q' ⟨j, by have := two_L_le_W r L hr; simp only [fbOutW_raw]; omega⟩ =
        if flag then (1 : ℕ).testBit j else false) ∧
      (∀ (j : ℕ) (hj : j < L), q' ⟨L + j, by have := two_L_le_W r L hr; simp only [fbOutW_raw]; omega⟩ =
        if flag then ((a + b) % M).testBit j else a.testBit j) ∧
      (∀ (j : ℕ) (hj : j < L), q' ⟨2 * L + j, by have := two_L_le_W r L hr; simp only [fbOutW_raw]; omega⟩ =
        if flag then false else b.testBit j) ∧
      (∀ (j : ℕ) (hj : j < L), q' ⟨3 * L + j, by have := two_L_le_W r L hr; simp only [fbOutW_raw]; omega⟩ =
        if flag then ((M + a - h_val) % M).testBit j else false) ∧
      (∀ (j : ℕ) (hj : j < L), q' ⟨4 * L + j, by have := two_L_le_W r L hr; simp only [fbOutW_raw]; omega⟩ =
        if flag then a.testBit j else false) ∧
      (∀ z : Fin (fbOutW_raw r L), 5 * L ≤ z.val → q' z = false) := by
  have h5 : 5 * L ≤ 3 * ((r + 1) * L) := five_L_le_three_W r L hr
  have hfwd := fbOutFwd_spec r M L a b h_val flag hr hL hM1 hML ha hb hh q hin
  have hunc := fbOutUnc_spec r M L a b h_val flag hr hL hM1 hML ha hb hh hflag0 _ hfwd
  set qu := evalRevList (fbOutUnc r M L hr hL) (evalRevList (fbOutFwd r M L hr hL) q)
  have hsw := fbOutSwap_spec r L hr qu hunc.2.2.2.2.2.1 hunc.2.2.2.2.2.2
  have hq'_eq : evalRevList (fbOutRev r M L hr hL) q = evalRevList (fbOutSwap r L hr) qu := by
    simp [fbOutRev, evalRevList_append, qu]
  rw [hq'_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, hsw.2⟩
  · intro j hj
    have heq : outAll_w r L j = out0_w r L j := by
      ext; rw [outAll_val (by omega), out0_val hj]
    rw [hsw.1 j (by omega), heq, hunc.1 j hj]
    cases j with
    | zero => rw [hfwd.out0_0]; cases flag <;> simp
    | succ k => rw [hfwd.out0_pos (k + 1) (by omega) hj]; cases flag <;> simp [testBit_one]
  · intro j hj
    have heq : outAll_w r L (L + j) = out1_w r L j := by
      ext; rw [outAll_val (by omega), out1_val hj]; omega
    rw [hsw.1 (L + j) (by omega), heq, hunc.2.1 j hj, hfwd.out1 j hj]
  · intro j hj
    have heq : outAll_w r L (2 * L + j) = out2_w r L j := by
      ext; rw [outAll_val (by omega), out2_val hj]; omega
    rw [hsw.1 (2 * L + j) (by omega), heq, hunc.2.2.1 j hj, hfwd.out2 j hj]
  · intro j hj
    have heq : outAll_w r L (3 * L + j) = out3_w r L j := by
      ext; rw [outAll_val (by omega), out3_val hj]; omega
    rw [hsw.1 (3 * L + j) (by omega), heq, hunc.2.2.2.1 j hj, hfwd.out3 j hj]
  · intro j hj
    have heq : outAll_w r L (4 * L + j) = out4_w r L j := by
      ext; rw [outAll_val (by omega), out4_val hj]; omega
    rw [hsw.1 (4 * L + j) (by omega), heq, hunc.2.2.2.2.1 j hj, hfwd.out4 j hj]

lemma bOutCode_eval_slot (D : FieldData) (y : D.BOutLabel) (k t : ℕ) (hk : k < 5) (ht : t < D.labW) :
    D.bOutCode y ⟨k * D.labW + t, by nlinarith⟩ =
      match y with
      | ⟨Sum.inl ab, _⟩ =>
        if k = 0 then false else if k = 1 then ab.1.val.testBit t
        else if k = 2 then ab.2.val.testBit t else false
      | ⟨Sum.inr γ, (d1, d2)⟩ =>
        if k = 0 then (1 : ℕ).testBit t else if k = 1 then γ.val.testBit t
        else if k = 2 then false else if k = 3 then d1.val.testBit t else d2.val.testBit t := by
  have hL : 0 < D.labW := fd_one_le_labW D
  have hdiv : (k * D.labW + t) / D.labW = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt ht, zero_add]
  have hmod : (k * D.labW + t) % D.labW = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases y with ⟨ab | γ, ⟨d1, d2⟩⟩ <;> dsimp only [FieldData.bOutCode, packNat] <;>
    rw [show (⟨(k * D.labW + t) / D.labW, by omega⟩ : Fin 5) = ⟨k, hk⟩ from Fin.ext hdiv, hmod] <;>
    rcases hk_cases with rfl | rfl | rfl | rfl | rfl <;>
    simp [Nat.zero_testBit]

def fbOutCirc (D : FieldData) : List (Instr (fbOutW_raw D.r D.labW)) :=
  compileRev (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))

lemma fbOutCirc_eval (D : FieldData) (p : D.Lab × D.Lab × Option D.Lab) :
    evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))
        (padTo (fbOutW_raw D.r D.labW) (bMidCode D p)) =
      padTo (fbOutW_raw D.r D.labW) (D.bOutCode (fbOutPerm D p)) := by
  have hL : 1 ≤ D.labW := fd_one_le_labW D
  have hW : 2 * D.labW ≤ (D.r + 1) * D.labW := two_L_le_W D.r D.labW D.hr
  have h5W : 5 * D.labW ≤ fbOutW_raw D.r D.labW := by
    have := five_L_le_three_W D.r D.labW D.hr
    simp only [fbOutW_raw]; omega
  have hq2 : 2 ≤ D.q := fd_q_ge_two D
  have hM1 : 1 ≤ D.q - 1 := by omega
  have hNe : NeZero (D.q - 1) := ⟨by omega⟩
  have hML : D.q - 1 < 2 ^ D.labW := fd_m_lt_two_pow_labW D
  have hin := bMidCode_padTo_spec D p
  have ha : p.1.val < D.q - 1 := @ZMod.val_lt (D.q - 1) hNe _
  have hb : p.2.1.val < D.q - 1 := @ZMod.val_lt (D.q - 1) hNe _
  have hh : Option.elim p.2.2 0 ZMod.val < D.q - 1 := by
    cases p.2.2 with
    | none => simp; omega
    | some η => exact @ZMod.val_lt (D.q - 1) hNe η
  have hflag0 : p.2.2.isSome = false → Option.elim p.2.2 0 ZMod.val = 0 := by
    cases p.2.2 <;> simp
  have hspec := fbOutRev_spec D.r (D.q - 1) D.labW p.1.val p.2.1.val
    (Option.elim p.2.2 0 ZMod.val) p.2.2.isSome D.hr hL hM1 hML ha hb hh hflag0 _ hin
  funext z
  by_cases hz5 : 5 * D.labW ≤ z.val
  · rw [hspec.2.2.2.2.2 z hz5]
    simp only [padTo, show ¬ (z.val < 5 * D.labW) by omega, ↓reduceDIte]
  · have hz_lt : z.val < 5 * D.labW := by omega
    have hk5 : z.val / D.labW < 5 := Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hz_lt)
    have htL : z.val % D.labW < D.labW := Nat.mod_lt z.val (by omega)
    have hdivmod : (z.val / D.labW) * D.labW + z.val % D.labW = z.val := by
      linarith [Nat.div_add_mod z.val D.labW]
    have hpad_rhs : padTo (fbOutW_raw D.r D.labW) (D.bOutCode (fbOutPerm D p)) z =
        D.bOutCode (fbOutPerm D p) ⟨z.val, hz_lt⟩ := by
      simp [padTo, hz_lt]
    rw [hpad_rhs]
    have hrhs_slot : (⟨z.val, hz_lt⟩ : Fin (5 * D.labW)) =
        ⟨(z.val / D.labW) * D.labW + z.val % D.labW, by nlinarith⟩ := Fin.ext hdivmod.symm
    rw [hrhs_slot, bOutCode_eval_slot D (fbOutPerm D p) (z.val / D.labW) (z.val % D.labW) hk5 htL]
    rcases p with ⟨α, β, η?⟩
    match hk_eq : z.val / D.labW with
    | 0 =>
      have hdiv_val : z.val = z.val % D.labW := by
        have h := hdivmod.symm; rw [hk_eq, Nat.zero_mul, Nat.zero_add] at h; exact h
      have hlt0 : z.val % D.labW < fbOutW_raw D.r D.labW := by rw [← hdiv_val]; exact z.isLt
      have hlhs : evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))
          (padTo (fbOutW_raw D.r D.labW) (bMidCode D (α, β, η?))) z =
        evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))
          (padTo (fbOutW_raw D.r D.labW) (bMidCode D (α, β, η?))) ⟨z.val % D.labW, hlt0⟩ :=
        congrArg _ (Fin.ext hdiv_val)
      rw [hlhs, hspec.1 (z.val % D.labW) htL]
      cases η? <;> dsimp only [fbOutPerm] <;>
        simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
    | 1 =>
      have hdiv_val : z.val = D.labW + z.val % D.labW := by
        have h := hdivmod.symm; rw [hk_eq, Nat.one_mul] at h; exact h
      have hlt1 : D.labW + z.val % D.labW < fbOutW_raw D.r D.labW := by rw [← hdiv_val]; exact z.isLt
      have hlhs : evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))
          (padTo (fbOutW_raw D.r D.labW) (bMidCode D (α, β, η?))) z =
        evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))
          (padTo (fbOutW_raw D.r D.labW) (bMidCode D (α, β, η?))) ⟨D.labW + z.val % D.labW, hlt1⟩ :=
        congrArg _ (Fin.ext hdiv_val)
      rw [hlhs, hspec.2.1 (z.val % D.labW) htL]
      cases η? with
      | none =>
        dsimp only [fbOutPerm]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.reduceEqDiff]
      | some η =>
        dsimp only [fbOutPerm]
        simp only [Option.isSome_some, ↓reduceIte, Nat.reduceEqDiff, ZMod.val_add]
    | 2 =>
      have hdiv_val : z.val = 2 * D.labW + z.val % D.labW := by
        have h := hdivmod.symm; rw [hk_eq] at h; exact h
      have hlt2 : 2 * D.labW + z.val % D.labW < fbOutW_raw D.r D.labW := by rw [← hdiv_val]; exact z.isLt
      have hlhs : evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))
          (padTo (fbOutW_raw D.r D.labW) (bMidCode D (α, β, η?))) z =
        evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))
          (padTo (fbOutW_raw D.r D.labW) (bMidCode D (α, β, η?))) ⟨2 * D.labW + z.val % D.labW, hlt2⟩ :=
        congrArg _ (Fin.ext hdiv_val)
      rw [hlhs, hspec.2.2.1 (z.val % D.labW) htL]
      cases η? <;> dsimp only [fbOutPerm] <;>
        simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte] <;> norm_num
    | 3 =>
      have hdiv_val : z.val = 3 * D.labW + z.val % D.labW := by
        have h := hdivmod.symm; rw [hk_eq] at h; exact h
      have hlt3 : 3 * D.labW + z.val % D.labW < fbOutW_raw D.r D.labW := by rw [← hdiv_val]; exact z.isLt
      have hlhs : evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))
          (padTo (fbOutW_raw D.r D.labW) (bMidCode D (α, β, η?))) z =
        evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))
          (padTo (fbOutW_raw D.r D.labW) (bMidCode D (α, β, η?))) ⟨3 * D.labW + z.val % D.labW, hlt3⟩ :=
        congrArg _ (Fin.ext hdiv_val)
      rw [hlhs, hspec.2.2.2.1 (z.val % D.labW) htL]
      cases η? with
      | none =>
        dsimp only [fbOutPerm]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.reduceEqDiff]
      | some η =>
        dsimp only [fbOutPerm]
        simp only [Option.isSome_some, Option.elim_some, ↓reduceIte, Nat.reduceEqDiff, zmod_val_sub hM1]
    | 4 =>
      have hdiv_val : z.val = 4 * D.labW + z.val % D.labW := by
        have h := hdivmod.symm; rw [hk_eq] at h; exact h
      have hlt4 : 4 * D.labW + z.val % D.labW < fbOutW_raw D.r D.labW := by rw [← hdiv_val]; exact z.isLt
      have hlhs : evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))
          (padTo (fbOutW_raw D.r D.labW) (bMidCode D (α, β, η?))) z =
        evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))
          (padTo (fbOutW_raw D.r D.labW) (bMidCode D (α, β, η?))) ⟨4 * D.labW + z.val % D.labW, hlt4⟩ :=
        congrArg _ (Fin.ext hdiv_val)
      rw [hlhs, hspec.2.2.2.2.1 (z.val % D.labW) htL]
      cases η? <;> dsimp only [fbOutPerm] <;>
        simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte] <;> norm_num
    | n + 5 =>
      rw [hk_eq] at hk5
      exact absurd hk5 (by omega)

lemma fbOutCirc_implements (D : FieldData) (k : ℕ) :
    Implements (circUnitary (fbOutCirc D))
      (fun x => padTo (fbOutW_raw D.r D.labW) (bMidCode D x))
      (fun y => padTo (fbOutW_raw D.r D.labW) (D.bOutCode y))
      (permMat (fbOutPerm D)) ((1 / 2 : ℝ) ^ k) := by
  have h1 : circUnitary (fbOutCirc D) =
      permMat (evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))) := by
    change circUnitary (compileRev (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))) = _
    exact circUnitary_compileRev (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D))
  rw [h1]
  exact @implements_of_permMat (D.Lab × D.Lab × Option D.Lab) D.BOutLabel _ _ _
    (fbOutW_raw D.r D.labW)
    (evalRevList (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D)))
    (fun x => padTo (fbOutW_raw D.r D.labW) (bMidCode D x))
    (fun y => padTo (fbOutW_raw D.r D.labW) (D.bOutCode y))
    (fbOutPerm D) (fbOutCirc_eval D) ((1 / 2 : ℝ) ^ k) (by positivity)

/-! ### Section 4: Raw circuit mirroring, length bounds, and `PolyTimeComputable` -/

def rawOfInstr {n : ℕ} : Instr n → ℕ × ℕ × ℕ
  | .h i => (0, i.val, 0)
  | .s i => (1, i.val, 0)
  | .t i => (2, i.val, 0)
  | .x i => (3, i.val, 0)
  | .cnot c t _ => (4, c.val, t.val)

def rawRevOf {n : ℕ} : RevGate n → ℕ × ℕ × ℕ × ℕ
  | .x i => (0, i.val, 0, 0)
  | .cnot c t _ => (1, c.val, t.val, 0)
  | .ccx a b t _ _ _ => (2, a.val, b.val, t.val)

def ccx3Raw : List (ℕ × ℕ × ℕ) := ccx3.map rawOfInstr

def rawCCX (a b t : ℕ) : List (ℕ × ℕ × ℕ) :=
  ccx3Raw.map (fun g =>
    let pick (k : ℕ) := if k = 0 then a else if k = 1 then b else t
    if g.1 = 4 then (4, pick g.2.1, pick g.2.2) else (g.1, pick g.2.1, 0))

lemma rawOfInstr_mapInstr_wire3 {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (g : Instr 3) :
    rawOfInstr (mapInstr (wire3 a b t hab hat hbt) g) =
      (let pick (k : ℕ) := if k = 0 then a.val else if k = 1 then b.val else t.val
       let r := rawOfInstr g
       if r.1 = 4 then (4, pick r.2.1, pick r.2.2) else (r.1, pick r.2.1, 0)) := by
  cases g with
  | h i => fin_cases i <;> rfl
  | s i => fin_cases i <;> rfl
  | t i => fin_cases i <;> rfl
  | x i => fin_cases i <;> rfl
  | cnot c d _ => fin_cases c <;> fin_cases d <;> rfl

def rawCompileRevGate (g : ℕ × ℕ × ℕ × ℕ) : List (ℕ × ℕ × ℕ) :=
  if g.1 = 0 then [(3, g.2.1, 0)]
  else if g.1 = 1 then [(4, g.2.1, g.2.2.1)]
  else rawCCX g.2.1 g.2.2.1 g.2.2.2

def rawCompileRev (cs : List (ℕ × ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  cs.flatMap rawCompileRevGate

lemma rawCompileRevGate_eq {n : ℕ} (g : RevGate n) :
    (compileRevGate g).map rawOfInstr = rawCompileRevGate (rawRevOf g) := by
  cases g with
  | x i => rfl
  | cnot c t h => rfl
  | ccx a b t hab hat hbt =>
    simp only [compileRevGate, mapCirc, List.map_map, rawCompileRevGate, rawRevOf, rawCCX, ccx3Raw]
    congr 1
    funext g
    exact rawOfInstr_mapInstr_wire3 a b t hab hat hbt g

lemma rawCompileRev_eq {n : ℕ} (cs : List (RevGate n)) :
    (compileRev cs).map rawOfInstr = rawCompileRev (cs.map rawRevOf) := by
  induction cs with
  | nil => rfl
  | cons g gs ih =>
    change (compileRevGate g ++ compileRev gs).map rawOfInstr =
      rawCompileRevGate (rawRevOf g) ++ rawCompileRev (gs.map rawRevOf)
    rw [List.map_append, rawCompileRevGate_eq, ih]

abbrev RegSpec := Bool × ℕ × ℕ × ℕ

def evalReg (s : RegSpec) (j : ℕ) : ℕ :=
  if s.1 then (if j < s.2.1 then s.2.2.1 + j else s.2.2.2)
  else s.2.2.1 + min j s.2.2.2

def rawInitNat (bitsM : List Bool) (sX : RegSpec) (rng : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  rng.flatMap (fun j => if bitsM[j]?.getD false then [(0, evalReg sX j, 0, 0)] else [])

def rawCCXLoop (ctrl : ℕ) (sSrc sDst : RegSpec) (rng : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  rng.map (fun j => (2, ctrl, evalReg sSrc j, evalReg sDst j))

def rawSwapLoop (sA sB : RegSpec) (rng : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  rng.flatMap (fun j => [(1, evalReg sA j, evalReg sB j, 0),
    (1, evalReg sB j, evalReg sA j, 0), (1, evalReg sA j, evalReg sB j, 0)])

def rawRippleAdd (sA sB sS sC : RegSpec) (rng : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  rng.flatMap (fun j =>
    [ (1, evalReg sA j, evalReg sS j, 0),
      (1, evalReg sB j, evalReg sS j, 0),
      (2, evalReg sA j, evalReg sB j, evalReg sC (j + 1)),
      (2, evalReg sC j, evalReg sS j, evalReg sC (j + 1)),
      (1, evalReg sC j, evalReg sS j, 0) ])

def rawRippleSub (sX sY sD sBr : RegSpec) (rng : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  rng.flatMap (fun j =>
    [ (1, evalReg sX j, evalReg sD j, 0),
      (0, evalReg sD j, 0, 0),
      (2, evalReg sD j, evalReg sY j, evalReg sBr (j + 1)),
      (1, evalReg sY j, evalReg sD j, 0),
      (2, evalReg sBr j, evalReg sD j, evalReg sBr (j + 1)),
      (0, evalReg sD j, 0, 0),
      (1, evalReg sBr j, evalReg sD j, 0) ])

def rawBase (r L : ℕ) : ℕ := 3 * ((r + 1) * L)
def rawW0 (_ _ : ℕ) : ℕ := 0
def rawWW (r L : ℕ) : ℕ := (r + 1) * L
def rawWireF (r L : ℕ) : ℕ := 2 * ((r + 1) * L)
def rawZA (r L : ℕ) : ℕ := rawBase r L + 13 * L + 10
def rawZB (r L : ℕ) : ℕ := rawBase r L + 13 * L + 11

def specRegA (_ L : ℕ) : RegSpec := (false, L, L, L)
def specRegB (r L : ℕ) : RegSpec := (false, L, (r + 1) * L + L, L)
def specRegH (r L : ℕ) : RegSpec := (false, L, 2 * ((r + 1) * L) + L, L)
def specOut0 (r L : ℕ) : RegSpec := (false, L, rawBase r L, L)
def specOut1 (r L : ℕ) : RegSpec := (false, L, rawBase r L + L, L)
def specOut2 (r L : ℕ) : RegSpec := (false, L, rawBase r L + 2 * L, L)
def specOut3 (r L : ℕ) : RegSpec := (false, L, rawBase r L + 3 * L, L)
def specOut4 (r L : ℕ) : RegSpec := (false, L, rawBase r L + 4 * L, L)
def specOutAll (r L : ℕ) : RegSpec := (false, L, rawBase r L, 5 * L)
def specLowAll (_ L : ℕ) : RegSpec := (false, L, 0, 5 * L)
def specTmp (r L : ℕ) : RegSpec := (false, L, rawBase r L + 5 * L, L)
def specRegM (r L : ℕ) : RegSpec := (false, L, rawBase r L + 6 * L, L)
def specRegS (r L : ℕ) : RegSpec := (false, L, rawBase r L + 7 * L + 1, L)
def specRegC (r L : ℕ) : RegSpec := (false, L, rawBase r L + 8 * L + 2, L + 1)
def specRegD1 (r L : ℕ) : RegSpec := (false, L, rawBase r L + 9 * L + 4, L)
def specRegBr1 (r L : ℕ) : RegSpec := (false, L, rawBase r L + 10 * L + 5, L + 1)
def specRegD2 (r L : ℕ) : RegSpec := (false, L, rawBase r L + 11 * L + 7, L)
def specRegBr2 (r L : ℕ) : RegSpec := (false, L, rawBase r L + 12 * L + 8, L + 1)
def specLift (s : RegSpec) (z : ℕ) : RegSpec := (true, s.2.1, s.2.2.1, z)

def rawAddModMPre (r L : ℕ) (bitsM : List Bool) (sX sY : RegSpec) (rngL1 : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  rawInitNat bitsM (specRegM r L) rngL1 ++
  rawRippleAdd sX sY (specRegS r L) (specRegC r L) rngL1 ++
  rawRippleSub (specRegS r L) (specRegM r L) (specRegD1 r L) (specRegBr1 r L) rngL1

def rawAddModMCopy (r L : ℕ) (sOut : RegSpec) (rngL : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  rawCCXLoop (evalReg (specRegBr1 r L) (L + 1)) (specRegS r L) sOut rngL ++
  [(0, evalReg (specRegBr1 r L) (L + 1), 0, 0)] ++
  rawCCXLoop (evalReg (specRegBr1 r L) (L + 1)) (specRegD1 r L) sOut rngL ++
  [(0, evalReg (specRegBr1 r L) (L + 1), 0, 0)]

def rawAddModM (r L : ℕ) (bitsM : List Bool) (sX sY sOut : RegSpec)
    (rngL rngL1 : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  let pre := rawAddModMPre r L bitsM sX sY rngL1
  pre ++ rawAddModMCopy r L sOut rngL ++ pre.reverse

def rawSubModMPre (r L : ℕ) (bitsM : List Bool) (sX sY : RegSpec) (rngL1 : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  rawInitNat bitsM (specRegM r L) rngL1 ++
  rawRippleAdd sX (specRegM r L) (specRegS r L) (specRegC r L) rngL1 ++
  rawRippleSub sX sY (specRegD1 r L) (specRegBr1 r L) rngL1 ++
  rawRippleSub (specRegS r L) sY (specRegD2 r L) (specRegBr2 r L) rngL1

def rawSubModMCopy (r L : ℕ) (sOut : RegSpec) (rngL : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  rawCCXLoop (evalReg (specRegBr1 r L) (L + 1)) (specRegD2 r L) sOut rngL ++
  [(0, evalReg (specRegBr1 r L) (L + 1), 0, 0)] ++
  rawCCXLoop (evalReg (specRegBr1 r L) (L + 1)) (specRegD1 r L) sOut rngL ++
  [(0, evalReg (specRegBr1 r L) (L + 1), 0, 0)]

def rawSubModM (r L : ℕ) (bitsM : List Bool) (sX sY sOut : RegSpec)
    (rngL rngL1 : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  let pre := rawSubModMPre r L bitsM sX sY rngL1
  pre ++ rawSubModMCopy r L sOut rngL ++ pre.reverse

def rawFbOutCCU (pre : List (ℕ × ℕ × ℕ × ℕ)) (ctrl : ℕ) (sSrc sDst : RegSpec)
    (rngL : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  pre ++ rawCCXLoop ctrl sSrc sDst rngL ++ pre.reverse

def rawFbOutFwd (r L : ℕ) (bitsM : List Bool) (rngL rngL1 : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  let wf := rawWireF r L
  let o0 := evalReg (specOut0 r L) 0
  let s1 := [(1, wf, o0, 0)]
  let s2 := [(0, wf, 0, 0)] ++
    rawCCXLoop wf (specRegA r L) (specOut1 r L) rngL ++
    rawCCXLoop wf (specRegB r L) (specOut2 r L) rngL ++
    [(0, wf, 0, 0)]
  let s3 := rawCCXLoop wf (specRegA r L) (specOut4 r L) rngL
  let s4 := rawFbOutCCU
    (rawAddModM r L bitsM (specLift (specRegA r L) (rawZA r L))
      (specLift (specRegB r L) (rawZB r L)) (specTmp r L) rngL rngL1)
    wf (specTmp r L) (specOut1 r L) rngL
  let s5 := rawFbOutCCU
    (rawSubModM r L bitsM (specLift (specRegA r L) (rawZA r L))
      (specLift (specRegH r L) (rawZB r L)) (specTmp r L) rngL rngL1)
    wf (specTmp r L) (specOut3 r L) rngL
  s1 ++ s2 ++ s3 ++ s4 ++ s5

def rawFbOutUnc (r L : ℕ) (bitsM : List Bool) (rngL rngL1 : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  let wf := rawWireF r L
  let o0 := evalReg (specOut0 r L) 0
  let s6 := rawCCXLoop o0 (specOut4 r L) (specRegA r L) rngL ++
    [(0, o0, 0, 0)] ++
    rawCCXLoop o0 (specOut1 r L) (specRegA r L) rngL ++
    [(0, o0, 0, 0)]
  let s7 := rawFbOutCCU
    (rawSubModM r L bitsM (specLift (specOut1 r L) (rawZA r L))
      (specLift (specOut4 r L) (rawZB r L)) (specTmp r L) rngL rngL1)
    o0 (specTmp r L) (specRegB r L) rngL
  let s8 := [(0, o0, 0, 0)] ++
    rawCCXLoop o0 (specOut2 r L) (specRegB r L) rngL ++
    [(0, o0, 0, 0)]
  let s9 := rawFbOutCCU
    (rawSubModM r L bitsM (specLift (specOut4 r L) (rawZA r L))
      (specLift (specOut3 r L) (rawZB r L)) (specTmp r L) rngL rngL1)
    o0 (specTmp r L) (specRegH r L) rngL
  let s10 := [(1, o0, wf, 0), (0, rawW0 r L, 0, 0), (0, rawWW r L, 0, 0)]
  s6 ++ s7 ++ s8 ++ s9 ++ s10

def rawFbOutSwap (r L : ℕ) (rng5L : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  rawSwapLoop (specOutAll r L) (specLowAll r L) rng5L

def rawFbOutRev (r L : ℕ) (bitsM : List Bool) (rngL rngL1 rng5L : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  rawFbOutFwd r L bitsM rngL rngL1 ++ rawFbOutUnc r L bitsM rngL rngL1 ++ rawFbOutSwap r L rng5L

lemma rawInitNat_eq {n : ℕ} (M k : ℕ) (X : ℕ → Fin n) (sX : RegSpec)
    (hX : ∀ j < k, (X j).val = evalReg sX j) (bitsM : List Bool)
    (hb : ∀ j < k, bitsM[j]?.getD false = M.testBit j) :
    (initNat M k X).map rawRevOf = rawInitNat bitsM sX (List.range k) := by
  unfold initNat rawInitNat
  have hgo : ∀ m ≤ k, (initNatGo M X m).map rawRevOf =
      (List.range m).flatMap (fun j => if bitsM[j]?.getD false then [(0, evalReg sX j, 0, 0)] else []) := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [initNatGo, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.map_append, ih (by omega)]
      congr 1
      rw [hb m hm]
      cases M.testBit m <;> simp [hX m hm, rawRevOf]
  exact hgo k le_rfl

lemma rawCCXLoop_eq {n : ℕ} (ctrl : Fin n) (src dst : ℕ → Fin n) (k : ℕ)
    (sSrc sDst : RegSpec)
    (hS : ∀ j < k, (src j).val = evalReg sSrc j)
    (hD : ∀ j < k, (dst j).val = evalReg sDst j)
    (hc1 : ∀ j < k, ctrl ≠ src j) (hc2 : ∀ j < k, ctrl ≠ dst j) (hsd : ∀ j < k, src j ≠ dst j) :
    (ccxLoop ctrl src dst k hc1 hc2 hsd).map rawRevOf =
      rawCCXLoop ctrl.val sSrc sDst (List.range k) := by
  unfold ccxLoop rawCCXLoop
  have hgo : ∀ m (hm : m ≤ k), (ccxLoopGo ctrl src dst hc1 hc2 hsd m hm).map rawRevOf =
      (List.range m).map (fun j => (2, ctrl.val, evalReg sSrc j, evalReg sDst j)) := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [ccxLoopGo, List.range_succ, List.map_append, List.map_append, ih (Nat.le_of_lt hm)]
      simp [hS m hm, hD m hm, rawRevOf]
  exact hgo k le_rfl

lemma rawSwapLoop_eq {n : ℕ} (A B : ℕ → Fin n) (k : ℕ) (sA sB : RegSpec)
    (hA : ∀ j < k, (A j).val = evalReg sA j)
    (hB : ∀ j < k, (B j).val = evalReg sB j)
    (hAB : ∀ j < k, A j ≠ B j) :
    (swapLoop A B k hAB).map rawRevOf =
      rawSwapLoop sA sB (List.range k) := by
  unfold swapLoop rawSwapLoop
  have hgo : ∀ m (hm : m ≤ k), (swapLoopGo A B hAB m hm).map rawRevOf =
      (List.range m).flatMap (fun j => [(1, evalReg sA j, evalReg sB j, 0),
        (1, evalReg sB j, evalReg sA j, 0), (1, evalReg sA j, evalReg sB j, 0)]) := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [swapLoopGo, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.map_append, ih (Nat.le_of_lt hm)]
      simp [hA m hm, hB m hm, swapRev, rawRevOf]
  exact hgo k le_rfl

lemma rawRippleAdd_eq {n k : ℕ} (w : AddWires n k) (sA sB sS sC : RegSpec)
    (hA : ∀ j < k, (w.A j).val = evalReg sA j)
    (hB : ∀ j < k, (w.B j).val = evalReg sB j)
    (hS : ∀ j < k, (w.S j).val = evalReg sS j)
    (hC : ∀ j ≤ k, (w.C j).val = evalReg sC j) :
    (rippleAdd w).map rawRevOf = rawRippleAdd sA sB sS sC (List.range k) := by
  unfold rippleAdd rawRippleAdd
  have hgo : ∀ m (hm : m ≤ k), (rippleAddGo w m hm).map rawRevOf =
      (List.range m).flatMap (fun j =>
        [ (1, evalReg sA j, evalReg sS j, 0),
          (1, evalReg sB j, evalReg sS j, 0),
          (2, evalReg sA j, evalReg sB j, evalReg sC (j + 1)),
          (2, evalReg sC j, evalReg sS j, evalReg sC (j + 1)),
          (1, evalReg sC j, evalReg sS j, 0) ]) := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [rippleAddGo, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.map_append, ih (Nat.le_of_lt hm)]
      simp [hA m hm, hB m hm, hS m hm, hC m (Nat.le_of_lt hm), hC (m + 1) hm, rippleAddStep, rawRevOf]
  exact hgo k le_rfl

lemma rawRippleSub_eq {n k : ℕ} (w : SubWires n k) (sX sY sD sBr : RegSpec)
    (hX : ∀ j < k, (w.X j).val = evalReg sX j)
    (hY : ∀ j < k, (w.Y j).val = evalReg sY j)
    (hD : ∀ j < k, (w.D j).val = evalReg sD j)
    (hBr : ∀ j ≤ k, (w.Br j).val = evalReg sBr j) :
    (rippleSub w).map rawRevOf = rawRippleSub sX sY sD sBr (List.range k) := by
  unfold rippleSub rawRippleSub
  have hgo : ∀ m (hm : m ≤ k), (rippleSubGo w m hm).map rawRevOf =
      (List.range m).flatMap (fun j =>
        [ (1, evalReg sX j, evalReg sD j, 0),
          (0, evalReg sD j, 0, 0),
          (2, evalReg sD j, evalReg sY j, evalReg sBr (j + 1)),
          (1, evalReg sY j, evalReg sD j, 0),
          (2, evalReg sBr j, evalReg sD j, evalReg sBr (j + 1)),
          (0, evalReg sD j, 0, 0),
          (1, evalReg sBr j, evalReg sD j, 0) ]) := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [rippleSubGo, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.map_append, ih (Nat.le_of_lt hm)]
      simp [hX m hm, hY m hm, hD m hm, hBr m (Nat.le_of_lt hm), hBr (m + 1) hm, rippleSubStep, rawRevOf]
  exact hgo k le_rfl

lemma evalReg_regM {r L j : ℕ} : (regM_w r L j).val = evalReg (specRegM r L) j := rfl
lemma evalReg_regS {r L j : ℕ} : (regS_w r L j).val = evalReg (specRegS r L) j := rfl
lemma evalReg_regC {r L j : ℕ} : (regC_w r L j).val = evalReg (specRegC r L) j := rfl
lemma evalReg_regD1 {r L j : ℕ} : (regD1_w r L j).val = evalReg (specRegD1 r L) j := rfl
lemma evalReg_regBr1 {r L j : ℕ} : (regBr1_w r L j).val = evalReg (specRegBr1 r L) j := rfl
lemma evalReg_regD2 {r L j : ℕ} : (regD2_w r L j).val = evalReg (specRegD2 r L) j := rfl
lemma evalReg_regBr2 {r L j : ℕ} : (regBr2_w r L j).val = evalReg (specRegBr2 r L) j := rfl
lemma evalReg_tmp {r L j : ℕ} : (tmp_w r L j).val = evalReg (specTmp r L) j := rfl
lemma evalReg_out0 {r L j : ℕ} : (out0_w r L j).val = evalReg (specOut0 r L) j := rfl
lemma evalReg_out1 {r L j : ℕ} : (out1_w r L j).val = evalReg (specOut1 r L) j := rfl
lemma evalReg_out2 {r L j : ℕ} : (out2_w r L j).val = evalReg (specOut2 r L) j := rfl
lemma evalReg_out3 {r L j : ℕ} : (out3_w r L j).val = evalReg (specOut3 r L) j := rfl
lemma evalReg_out4 {r L j : ℕ} : (out4_w r L j).val = evalReg (specOut4 r L) j := rfl
lemma evalReg_outAll {r L j : ℕ} : (outAll_w r L j).val = evalReg (specOutAll r L) j := rfl
lemma evalReg_lowAll {r L j : ℕ} : (lowAll_w r L j).val = evalReg (specLowAll r L) j := by
  simp [lowAll_w, evalReg, specLowAll]
lemma evalReg_regA {r L j : ℕ} : (regA_w r L j).val = evalReg (specRegA r L) j := rfl
lemma evalReg_regB {r L j : ℕ} : (regB_w r L j).val = evalReg (specRegB r L) j := rfl
lemma evalReg_regH {r L j : ℕ} : (regH_w r L j).val = evalReg (specRegH r L) j := rfl

lemma evalReg_lift {r L : ℕ} (X : ℕ → Fin (fbOutW_raw r L)) (sX : RegSpec)
    (hLen : sX.1 = false ∧ sX.2.1 = L ∧ sX.2.2.2 = L)
    (hX : ∀ j, (X j).val = evalReg sX j) (z : Fin (fbOutW_raw r L)) (j : ℕ) :
    (liftReg L X z j).val = evalReg (specLift sX z.val) j := by
  dsimp only [liftReg, evalReg, specLift]
  rw [if_pos rfl, hLen.2.1]
  split_ifs with hj
  · rw [hX j, evalReg, if_neg (by rw [hLen.1]; decide), hLen.2.2, min_eq_left (Nat.le_of_lt hj)]
  · rfl

lemma rawAddModM_eq {r L : ℕ} (M : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (hIO : ValidModIO r L X Y Out) (sX sY sOut : RegSpec)
    (hX : ∀ j < L + 1, (X j).val = evalReg sX j)
    (hY : ∀ j < L + 1, (Y j).val = evalReg sY j)
    (hOut : ∀ j < L, (Out j).val = evalReg sOut j)
    (bitsM : List Bool) (hb : ∀ j < L + 1, bitsM[j]?.getD false = M.testBit j) :
    (addModM M X Y Out hIO).map rawRevOf =
      rawAddModM r L bitsM sX sY sOut (List.range L) (List.range (L + 1)) := by
  unfold addModM addModMPre addModMCopy rawAddModM rawAddModMPre rawAddModMCopy
  have h1 := rawInitNat_eq M (L + 1) (regM_w r L) (specRegM r L) (fun _ _ => evalReg_regM) bitsM hb
  have h2 := rawRippleAdd_eq (mkAdd_XY_S X Y Out hIO) sX sY (specRegS r L) (specRegC r L)
    hX hY (fun _ _ => evalReg_regS) (fun _ _ => evalReg_regC)
  have h3 := rawRippleSub_eq (mkSub_SM_D1 r L) (specRegS r L) (specRegM r L) (specRegD1 r L) (specRegBr1 r L)
    (fun _ _ => evalReg_regS) (fun _ _ => evalReg_regM) (fun _ _ => evalReg_regD1) (fun _ _ => evalReg_regBr1)
  simp only [List.map_append, List.map_reverse, List.map_cons, List.map_nil, h1, h2, h3,
    rawCCXLoop_eq _ _ _ _ (specRegS r L) sOut (fun _ _ => evalReg_regS) hOut,
    rawCCXLoop_eq _ _ _ _ (specRegD1 r L) sOut (fun _ _ => evalReg_regD1) hOut]
  rfl

lemma rawSubModM_eq {r L : ℕ} (M : ℕ) (X Y Out : ℕ → Fin (fbOutW_raw r L))
    (hIO : ValidModIO r L X Y Out) (sX sY sOut : RegSpec)
    (hX : ∀ j < L + 1, (X j).val = evalReg sX j)
    (hY : ∀ j < L + 1, (Y j).val = evalReg sY j)
    (hOut : ∀ j < L, (Out j).val = evalReg sOut j)
    (bitsM : List Bool) (hb : ∀ j < L + 1, bitsM[j]?.getD false = M.testBit j) :
    (subModM M X Y Out hIO).map rawRevOf =
      rawSubModM r L bitsM sX sY sOut (List.range L) (List.range (L + 1)) := by
  unfold subModM subModMPre subModMCopy rawSubModM rawSubModMPre rawSubModMCopy
  have h1 := rawInitNat_eq M (L + 1) (regM_w r L) (specRegM r L) (fun _ _ => evalReg_regM) bitsM hb
  have h2 := rawRippleAdd_eq (mkAdd_XM_S X Y Out hIO) sX (specRegM r L) (specRegS r L) (specRegC r L)
    hX (fun _ _ => evalReg_regM) (fun _ _ => evalReg_regS) (fun _ _ => evalReg_regC)
  have h3 := rawRippleSub_eq (mkSub_XY_D1 X Y Out hIO) sX sY (specRegD1 r L) (specRegBr1 r L)
    hX hY (fun _ _ => evalReg_regD1) (fun _ _ => evalReg_regBr1)
  have h4 := rawRippleSub_eq (mkSub_SY_D2 X Y Out hIO) (specRegS r L) sY (specRegD2 r L) (specRegBr2 r L)
    (fun _ _ => evalReg_regS) hY (fun _ _ => evalReg_regD2) (fun _ _ => evalReg_regBr2)
  simp only [List.map_append, List.map_reverse, List.map_cons, List.map_nil, h1, h2, h3, h4,
    rawCCXLoop_eq _ _ _ _ (specRegD2 r L) sOut (fun _ _ => evalReg_regD2) hOut,
    rawCCXLoop_eq _ _ _ _ (specRegD1 r L) sOut (fun _ _ => evalReg_regD1) hOut]
  rfl

lemma rawFbOutCCU_eq {n : ℕ} (L : ℕ) (pre : List (RevGate n)) (ctrl : Fin n) (src dst : ℕ → Fin n)
    (sSrc sDst : RegSpec)
    (hS : ∀ j < L, (src j).val = evalReg sSrc j)
    (hD : ∀ j < L, (dst j).val = evalReg sDst j)
    (hcs : ∀ j < L, ctrl ≠ src j) (hcd : ∀ j < L, ctrl ≠ dst j) (hsd : ∀ j < L, src j ≠ dst j) :
    (fbOutCCU L pre ctrl src dst hcs hcd hsd).map rawRevOf =
      rawFbOutCCU (pre.map rawRevOf) ctrl.val sSrc sDst (List.range L) := by
  unfold fbOutCCU rawFbOutCCU
  simp only [List.map_append, List.map_reverse, rawCCXLoop_eq ctrl src dst L sSrc sDst hS hD hcs hcd hsd]

lemma rawFbOutRev_eq (r M L : ℕ) (hr : 1 ≤ r) (hL : 1 ≤ L) (bitsM : List Bool)
    (hb : ∀ j < L + 1, bitsM[j]?.getD false = M.testBit j) :
    (fbOutRev r M L hr hL).map rawRevOf =
      rawFbOutRev r L bitsM (List.range L) (List.range (L + 1)) (List.range (5 * L)) := by
  unfold fbOutRev fbOutFwd fbOutUnc fbOutSwap rawFbOutRev rawFbOutFwd rawFbOutUnc rawFbOutSwap
  have hLA : ∀ j, (liftReg L (regA_w r L) (zA_w r L) j).val = evalReg (specLift (specRegA r L) (rawZA r L)) j :=
    fun j => evalReg_lift (regA_w r L) (specRegA r L) ⟨rfl, rfl, rfl⟩ (fun _ => evalReg_regA) (zA_w r L) j
  have hLB : ∀ j, (liftReg L (regB_w r L) (zB_w r L) j).val = evalReg (specLift (specRegB r L) (rawZB r L)) j :=
    fun j => evalReg_lift (regB_w r L) (specRegB r L) ⟨rfl, rfl, rfl⟩ (fun _ => evalReg_regB) (zB_w r L) j
  have hLH : ∀ j, (liftReg L (regH_w r L) (zB_w r L) j).val = evalReg (specLift (specRegH r L) (rawZB r L)) j :=
    fun j => evalReg_lift (regH_w r L) (specRegH r L) ⟨rfl, rfl, rfl⟩ (fun _ => evalReg_regH) (zB_w r L) j
  have hL1 : ∀ j, (liftReg L (out1_w r L) (zA_w r L) j).val = evalReg (specLift (specOut1 r L) (rawZA r L)) j :=
    fun j => evalReg_lift (out1_w r L) (specOut1 r L) ⟨rfl, rfl, rfl⟩ (fun _ => evalReg_out1) (zA_w r L) j
  have hL4A : ∀ j, (liftReg L (out4_w r L) (zA_w r L) j).val = evalReg (specLift (specOut4 r L) (rawZA r L)) j :=
    fun j => evalReg_lift (out4_w r L) (specOut4 r L) ⟨rfl, rfl, rfl⟩ (fun _ => evalReg_out4) (zA_w r L) j
  have hL4B : ∀ j, (liftReg L (out4_w r L) (zB_w r L) j).val = evalReg (specLift (specOut4 r L) (rawZB r L)) j :=
    fun j => evalReg_lift (out4_w r L) (specOut4 r L) ⟨rfl, rfl, rfl⟩ (fun _ => evalReg_out4) (zB_w r L) j
  have hL3 : ∀ j, (liftReg L (out3_w r L) (zB_w r L) j).val = evalReg (specLift (specOut3 r L) (rawZB r L)) j :=
    fun j => evalReg_lift (out3_w r L) (specOut3 r L) ⟨rfl, rfl, rfl⟩ (fun _ => evalReg_out3) (zB_w r L) j
  have ha1 := rawAddModM_eq M _ _ _ (hIO_AB r L hr) _ _ _ (fun j _ => hLA j) (fun j _ => hLB j) (fun _ _ => evalReg_tmp) bitsM hb
  have hs1 := rawSubModM_eq M _ _ _ (hIO_AH r L hr) _ _ _ (fun j _ => hLA j) (fun j _ => hLH j) (fun _ _ => evalReg_tmp) bitsM hb
  have hs2 := rawSubModM_eq M _ _ _ (hIO_14 r L) _ _ _ (fun j _ => hL1 j) (fun j _ => hL4B j) (fun _ _ => evalReg_tmp) bitsM hb
  have hs3 := rawSubModM_eq M _ _ _ (hIO_43 r L) _ _ _ (fun j _ => hL4A j) (fun j _ => hL3 j) (fun _ _ => evalReg_tmp) bitsM hb
  simp only [List.map_append, List.map_cons, List.map_nil,
    rawFbOutCCU_eq _ _ _ _ _ _ _ (fun _ _ => evalReg_tmp) (fun _ _ => evalReg_out1),
    rawFbOutCCU_eq _ _ _ _ _ _ _ (fun _ _ => evalReg_tmp) (fun _ _ => evalReg_out3),
    rawFbOutCCU_eq _ _ _ _ _ _ _ (fun _ _ => evalReg_tmp) (fun _ _ => evalReg_regB),
    rawFbOutCCU_eq _ _ _ _ _ _ _ (fun _ _ => evalReg_tmp) (fun _ _ => evalReg_regH),
    ha1, hs1, hs2, hs3,
    rawCCXLoop_eq _ _ _ _ _ _ (fun _ _ => evalReg_regA) (fun _ _ => evalReg_out1),
    rawCCXLoop_eq _ _ _ _ _ _ (fun _ _ => evalReg_regB) (fun _ _ => evalReg_out2),
    rawCCXLoop_eq _ _ _ _ _ _ (fun _ _ => evalReg_regA) (fun _ _ => evalReg_out4),
    rawCCXLoop_eq _ _ _ _ _ _ (fun _ _ => evalReg_out4) (fun _ _ => evalReg_regA),
    rawCCXLoop_eq _ _ _ _ _ _ (fun _ _ => evalReg_out1) (fun _ _ => evalReg_regA),
    rawCCXLoop_eq _ _ _ _ _ _ (fun _ _ => evalReg_out2) (fun _ _ => evalReg_regB),
    rawSwapLoop_eq _ _ _ _ _ (fun _ _ => evalReg_outAll) (fun _ _ => evalReg_lowAll)]
  rfl

section Section4_Poly

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime

lemma polyProgram_id_of_poly {f : List Bool → List Bool} (hf : Automatic.Poly f) :
    PolyTimeComputable f := by
  have hp : PolyProgram id id f :=
    ((BooleanLists.packProgram.comp hf.program).comp BooleanLists.unpackProgram).congr
      f (fun _ => rfl)
  exact ⟨hp.stock⟩

@[simp] lemma enc_nat_eq (n : ℕ) : (Coding.encode n : List Bool) = n.bits := rfl
@[simp] lemma enc_bool_eq (b : Bool) : (Coding.encode b : List Bool) = encodeBool b := rfl
@[simp] lemma enc_pair_eq {α β : Type} [Coding α] [Coding β] (x : α × β) :
    (Coding.encode x : List Bool) = encodePair Coding.encode Coding.encode x := rfl
@[simp] lemma enc_list_eq {α : Type} [Coding α] (xs : List α) :
    (Coding.encode xs : List Bool) = encodeList Coding.encode xs := rfl

lemma listFoldLinear_poly {α β γ : Type} [Coding α] [Coding β] [Coding γ]
    {f : β → γ → β} {as : α → List γ} {b0 : α → β} (g0 : γ) (C : ℕ)
    (hf : Automatic.Poly (fun x : β × γ => f x.1 x.2))
    (hop : ∀ b g, (Coding.encode (f b g)).length ≤
      (Coding.encode b).length + C * (2 * (Coding.encode g).length + 1))
    (ha : Automatic.Poly as) (hb : Automatic.Poly b0) :
    Automatic.Poly (fun x => (as x).foldl f (b0 x)) := by
  let P : PolyProgram (encodePair Coding.encode Coding.encode) Coding.encode
      (fun x : β × γ => f x.1 x.2) := hf.program
  exact Automatic.Poly.comp ⟨P.listFoldLinear g0 C hop⟩ (Automatic.Poly.pair ha hb)

lemma listFold_poly {α β γ : Type} [Coding α] [Coding β] [Coding γ]
    {f : β → γ → β} {as : α → List γ} {b0 : α → β} (g0 : γ) (B : Polynomial ℕ)
    (hf : Automatic.Poly (fun x : β × γ => f x.1 x.2))
    (hB : ∀ (gs : List γ) (b : β) pre suf, gs = pre ++ suf →
      (Coding.encode (pre.foldl f b)).length ≤
        B.eval (encodePair (encodeList Coding.encode) Coding.encode (gs, b)).length)
    (ha : Automatic.Poly as) (hb : Automatic.Poly b0) :
    Automatic.Poly (fun x => (as x).foldl f (b0 x)) := by
  let P : PolyProgram (encodePair Coding.encode Coding.encode) Coding.encode
      (fun x : β × γ => f x.1 x.2) := hf.program
  exact Automatic.Poly.comp ⟨P.listFold g0 B hB⟩ (Automatic.Poly.pair ha hb)

@[fun_prop] theorem nat_div : Automatic.Poly (fun x : ℕ × ℕ => x.1 / x.2) := ⟨PolyProgram.natDiv⟩
@[fun_prop] theorem nat_mod : Automatic.Poly (fun x : ℕ × ℕ => x.1 % x.2) := ⟨PolyProgram.natMod⟩
@[fun_prop] theorem nat_div_comp {α : Type} [Coding α] {f g : α → ℕ}
    (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun x => f x / g x) :=
  Automatic.Poly.comp nat_div (Automatic.Poly.pair hf hg)
@[fun_prop] theorem nat_mod_comp {α : Type} [Coding α] {f g : α → ℕ}
    (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun x => f x % g x) :=
  Automatic.Poly.comp nat_mod (Automatic.Poly.pair hf hg)
@[fun_prop] theorem nat_add_comp {α : Type} [Coding α] {f g : α → ℕ}
    (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun x => f x + g x) :=
  Automatic.Poly.comp Automatic.Poly.nat_add (Automatic.Poly.pair hf hg)
@[fun_prop] theorem nat_sub_comp {α : Type} [Coding α] {f g : α → ℕ}
    (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun x => f x - g x) :=
  Automatic.Poly.comp Automatic.Poly.nat_sub (Automatic.Poly.pair hf hg)
@[fun_prop] theorem nat_mul_comp {α : Type} [Coding α] {f g : α → ℕ}
    (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun x => f x * g x) :=
  Automatic.Poly.comp Automatic.Poly.nat_mul (Automatic.Poly.pair hf hg)
@[fun_prop] theorem nat_min_comp {α : Type} [Coding α] {f g : α → ℕ}
    (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun x => min (f x) (g x)) := by
  have h : (fun x => min (f x) (g x)) = (fun x => if f x ≤ g x then f x else g x) :=
    funext (fun _ => Nat.min_def)
  rw [h]; fun_prop
@[fun_prop] theorem list_append_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f g : α → List β} (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun x => f x ++ g x) :=
  Automatic.Poly.comp Automatic.Poly.list_append (Automatic.Poly.pair hf hg)
@[fun_prop] theorem list_take_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → List β} {n : α → ℕ} (hf : Automatic.Poly f) (hn : Automatic.Poly n) :
    Automatic.Poly (fun x => (f x).take (n x)) :=
  Automatic.Poly.comp parser_take_poly (Automatic.Poly.pair hf hn)
@[fun_prop] theorem list_indices_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → List β} (hf : Automatic.Poly f) :
    Automatic.Poly (fun x => List.range (f x).length) :=
  Automatic.Poly.comp (f := fun xs : List β => List.range xs.length) Automatic.Poly.list_indices hf
@[fun_prop] theorem list_reverse_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → List β} (hf : Automatic.Poly f) :
    Automatic.Poly (fun x => (f x).reverse) :=
  Automatic.Poly.comp parser_reverse_poly hf
@[fun_prop] theorem list_length_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → List β} (hf : Automatic.Poly f) :
    Automatic.Poly (fun x => (f x).length) :=
  Automatic.Poly.comp Automatic.Poly.list_length hf
@[fun_prop] theorem list_cons_comp {α β : Type} [Coding α] [Coding β]
    {a : α → β} {as : α → List β} (ha : Automatic.Poly a) (has : Automatic.Poly as) :
    Automatic.Poly (fun x => a x :: as x) :=
  Automatic.Poly.comp Automatic.Poly.list_cons (Automatic.Poly.pair ha has)
@[fun_prop] theorem bool_and_comp {α : Type} [Coding α] {f g : α → Bool}
    (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun x => f x && g x) :=
  Automatic.Poly.comp Automatic.Poly.bool_and (Automatic.Poly.pair hf hg)
@[fun_prop] theorem bool_or_comp {α : Type} [Coding α] {f g : α → Bool}
    (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun x => f x || g x) :=
  Automatic.Poly.comp Automatic.Poly.bool_or (Automatic.Poly.pair hf hg)
@[fun_prop] theorem bool_not_comp {α : Type} [Coding α] {f : α → Bool}
    (hf : Automatic.Poly f) :
    Automatic.Poly (fun x => !(f x)) :=
  Automatic.Poly.comp Automatic.Poly.bool_not hf

def parsePRStep (st : ℕ × List Bool × List Bool) (b : Bool) : ℕ × List Bool × List Bool :=
  if st.1 = 0 then (if b then (1, st.2.1, st.2.2) else (2, st.2.1, st.2.2))
  else if st.1 = 1 then (0, b :: st.2.1, st.2.2)
  else if st.1 = 2 then (3, st.2.1, st.2.2)
  else if st.1 = 3 then (if b then (4, st.2.1, st.2.2) else (5, st.2.1, st.2.2))
  else if st.1 = 4 then (3, st.2.1, b :: st.2.2)
  else (5, st.2.1, st.2.2)

def parsePR (xs : List Bool) : ℕ × ℕ :=
  let st := xs.foldl parsePRStep (0, [], [])
  (bitValue st.2.1.reverse, bitValue st.2.2.reverse)

lemma parsePRStep_poly :
    Automatic.Poly (fun x : (ℕ × List Bool × List Bool) × Bool => parsePRStep x.1 x.2) := by
  unfold parsePRStep
  fun_prop

lemma parsePRStep_len (b : ℕ × List Bool × List Bool) (g : Bool) :
    (Coding.encode (parsePRStep b g)).length ≤
      (Coding.encode b).length + 4 * (2 * (Coding.encode g).length + 1) := by
  have hb0 : (0 : ℕ).bits.length = 0 := by decide
  have hb1 : (1 : ℕ).bits.length = 1 := by decide
  have hb2 : (2 : ℕ).bits.length = 2 := by decide
  have hb3 : (3 : ℕ).bits.length = 2 := by decide
  have hb4 : (4 : ℕ).bits.length = 3 := by decide
  have hb5 : (5 : ℕ).bits.length = 3 := by decide
  have hbl : ∀ (c : Bool) (xs : List Bool),
      (encodeList (Coding.encode : Bool → List Bool) (c :: xs)).length =
        3 + (encodeList Coding.encode xs).length := by
    intro c xs
    rw [EncodedList.cons_length, enc_bool_eq]
    simp only [encodeBool, List.length_singleton]
  rcases b with ⟨ph, pbs, rbs⟩
  unfold parsePRStep
  split_ifs <;>
    simp only [enc_pair_eq, enc_nat_eq, enc_list_eq, enc_bool_eq, encodePair_length,
      encodeBool, List.length_singleton, hb0, hb1, hb2, hb3, hb4, hb5, hbl] <;>
    omega

@[fun_prop] lemma parsePR_poly : Automatic.Poly parsePR := by
  unfold parsePR
  dsimp only
  have hfold : Automatic.Poly (fun xs : List Bool => xs.foldl parsePRStep (0, [], [])) :=
    listFoldLinear_poly false 4 parsePRStep_poly parsePRStep_len
      Automatic.Poly.identity (Automatic.Poly.const (0, [], []))
  fun_prop

lemma parsePR_fold_bits1 (bs : List Bool) (acc r : List Bool) :
    (bs.flatMap (fun β => [true, β])).foldl parsePRStep (0, acc, r) =
      (0, bs.reverse ++ acc, r) := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append,
      List.foldl_cons, List.reverse_cons, List.append_assoc]
    have hstep : parsePRStep (parsePRStep (0, acc, r) true) b = (0, b :: acc, r) := by
      simp [parsePRStep]
    rw [hstep]
    simpa [List.append_assoc] using ih (b :: acc)

lemma parsePR_fold_bits2 (bs : List Bool) (p acc : List Bool) :
    (bs.flatMap (fun β => [true, β])).foldl parsePRStep (3, p, acc) =
      (3, p, bs.reverse ++ acc) := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append,
      List.foldl_cons, List.reverse_cons, List.append_assoc]
    have hstep : parsePRStep (parsePRStep (3, p, acc) true) b = (3, p, b :: acc) := by
      simp [parsePRStep]
    rw [hstep]
    simpa [List.append_assoc] using ih (b :: acc)

lemma parsePR_fold_done (tail : List Bool) (p r : List Bool) :
    tail.foldl parsePRStep (5, p, r) = (5, p, r) := by
  induction tail with
  | nil => rfl
  | cons b tail ih =>
    rw [List.foldl_cons]
    have hstep : parsePRStep (5, p, r) b = (5, p, r) := by simp [parsePRStep]
    rw [hstep]
    exact ih

lemma parsePR_encData (D : FieldData) (tail : List Bool) :
    parsePR (D.encData ++ tail) = (D.p, D.r) := by
  unfold parsePR GL2QFT.FieldData.encData QAlgorithms.LocalHamiltonian.encBin
  simp only [List.append_assoc, List.foldl_append]
  rw [parsePR_fold_bits1 D.p.bits [] []]
  have hd1 : ([false, false].foldl parsePRStep (0, D.p.bits.reverse ++ [], [])) =
      (3, D.p.bits.reverse, []) := by
    simp [parsePRStep]
  rw [hd1, parsePR_fold_bits2 D.r.bits D.p.bits.reverse []]
  have hd2 : ([false, false].foldl parsePRStep (3, D.p.bits.reverse, D.r.bits.reverse ++ [])) =
      (5, D.p.bits.reverse, D.r.bits.reverse) := by
    simp [parsePRStep]
  rw [hd2]
  simp only [parsePR_fold_done, List.reverse_reverse, bitValue_eq_word, Word.value_bits]

def powStep (st : ℕ × ℕ) (_ : ℕ) : ℕ × ℕ := (st.1 * st.2, st.2)

def powBounded (p r : ℕ) (rng : List ℕ) : ℕ :=
  ((rng.take r).foldl powStep (1, p)).1

lemma powStep_poly : Automatic.Poly (fun x : (ℕ × ℕ) × ℕ => powStep x.1 x.2) := by
  unfold powStep; fun_prop

lemma powStep_foldl (pre : List ℕ) (b : ℕ × ℕ) :
    pre.foldl powStep b = (b.1 * b.2 ^ pre.length, b.2) := by
  induction pre generalizing b with
  | nil => simp
  | cons _ pre ih =>
    simp only [List.foldl_cons, powStep, ih, List.length_cons, pow_succ', mul_assoc]

lemma bits_len_mul_pow (a x k : ℕ) :
    (a * x ^ k).bits.length ≤ a.bits.length + k * x.bits.length := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc]
    have h := NatBinary.mul_length (a * x ^ k) x
    rw [Nat.succ_mul]
    omega

lemma powStep_bound (gs : List ℕ) (b : ℕ × ℕ) (pre suf : List ℕ) (he : gs = pre ++ suf) :
    (Coding.encode (pre.foldl powStep b)).length ≤
      (Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 1).eval
        (encodePair (encodeList Coding.encode) Coding.encode (gs, b)).length := by
  rw [powStep_foldl]
  have hcb : (encodeList (Coding.encode : ℕ → List Bool) gs).length = (encodeList Nat.bits gs).length := rfl
  have hpre : pre.length ≤ gs.length := by rw [he, List.length_append]; omega
  have hgs : gs.length ≤ (encodeList Nat.bits gs).length := EncodedList.length_le Nat.bits gs
  have hm := bits_len_mul_pow b.1 b.2 pre.length
  have hl : (encodePair (encodeList Coding.encode) Coding.encode (gs, b)).length =
      2 * (encodeList Nat.bits gs).length + 1 + (2 * b.1.bits.length + 1 + b.2.bits.length) := by
    simp only [enc_pair_eq, enc_nat_eq, encodePair_length, hcb]
  have hmul : pre.length * b.2.bits.length ≤
      (encodePair (encodeList Coding.encode) Coding.encode (gs, b)).length *
        (encodePair (encodeList Coding.encode) Coding.encode (gs, b)).length := by
    nlinarith
  simp only [enc_pair_eq, enc_nat_eq, encodePair_length,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, hcb]
  nlinarith

@[fun_prop] lemma powBounded_comp {α : Type} [Coding α] {p r : α → ℕ} {rng : α → List ℕ}
    (hp : Automatic.Poly p) (hr : Automatic.Poly r) (hrng : Automatic.Poly rng) :
    Automatic.Poly (fun x => powBounded (p x) (r x) (rng x)) := by
  unfold powBounded
  have hfold : Automatic.Poly (fun x => ((rng x).take (r x)).foldl powStep (1, p x)) :=
    listFold_poly 0 (Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 1)
      powStep_poly powStep_bound (by fun_prop) (by fun_prop)
  fun_prop

lemma powBounded_eq (p r : ℕ) (rng : List ℕ) (hr : r ≤ rng.length) :
    powBounded p r rng = p ^ r := by
  unfold powBounded
  rw [powStep_foldl, List.length_take, Nat.min_eq_left hr, one_mul]

def clogStep (st : Bool × ℕ × ℕ × ℕ) (_ : ℕ) : Bool × ℕ × ℕ × ℕ :=
  if st.1 then st
  else if st.2.2.2 ≤ st.2.2.1 then (true, st.2.1, st.2.2.1, st.2.2.2)
  else (false, st.2.1 + 1, 2 * st.2.2.1, st.2.2.2)

def clog2Bounded (n : ℕ) (rng : List ℕ) : ℕ :=
  (rng.foldl clogStep (false, 0, 1, n)).2.1

lemma clogStep_poly :
    Automatic.Poly (fun x : (Bool × ℕ × ℕ × ℕ) × ℕ => clogStep x.1 x.2) := by
  unfold clogStep; fun_prop

lemma clogStep_len (b : Bool × ℕ × ℕ × ℕ) (g : ℕ) :
    (Coding.encode (clogStep b g)).length ≤
      (Coding.encode b).length + 8 * (2 * (Coding.encode g).length + 1) := by
  have hb1 : (1 : ℕ).bits.length = 1 := by decide
  have hb2 : (2 : ℕ).bits.length = 2 := by decide
  have ha := NatBinary.add_length b.2.1 1
  have hm := NatBinary.mul_length 2 b.2.2.1
  rcases b with ⟨flg, k, p, tgt⟩
  unfold clogStep
  split_ifs <;>
    simp only [enc_pair_eq, enc_nat_eq, enc_bool_eq, encodePair_length,
      encodeBool, List.length_singleton] at ha hm ⊢ <;>
    omega

@[fun_prop] lemma clog2Bounded_comp {α : Type} [Coding α] {n : α → ℕ} {rng : α → List ℕ}
    (hn : Automatic.Poly n) (hrng : Automatic.Poly rng) :
    Automatic.Poly (fun x => clog2Bounded (n x) (rng x)) := by
  unfold clog2Bounded
  have hfold : Automatic.Poly (fun x => (rng x).foldl clogStep (false, 0, 1, n x)) :=
    listFoldLinear_poly 0 8 clogStep_poly clogStep_len hrng (by fun_prop)
  fun_prop

lemma clogStep_foldl_lt (xs : List ℕ) (j n : ℕ) (hj : j + xs.length ≤ Nat.clog 2 n) :
    xs.foldl clogStep (false, j, 2 ^ j, n) =
      (false, j + xs.length, 2 ^ (j + xs.length), n) := by
  induction xs generalizing j with
  | nil => simp
  | cons _ xs ih =>
    simp only [List.foldl_cons, clogStep, Bool.false_eq_true, ↓reduceIte, List.length_cons] at *
    have hnot : ¬ n ≤ 2 ^ j := by
      intro hle
      have hcl : Nat.clog 2 n ≤ j := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hle
      omega
    rw [if_neg hnot]
    have hpow : 2 * 2 ^ j = 2 ^ (j + 1) := by ring
    rw [hpow]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (j + 1) (by omega)

lemma clog2Bounded_eq (n : ℕ) (rng : List ℕ) (h : Nat.clog 2 n + 1 ≤ rng.length) :
    clog2Bounded n rng = Nat.clog 2 n := by
  unfold clog2Bounded
  have htake : (rng.take (Nat.clog 2 n)).length = Nat.clog 2 n := by
    simp [Nat.min_eq_left (by omega : Nat.clog 2 n ≤ rng.length)]
  have hdrop : rng.drop (Nat.clog 2 n) ≠ [] := by
    intro hnil
    have hl : (rng.drop (Nat.clog 2 n)).length = 0 := by simp [hnil]
    rw [List.length_drop] at hl
    omega
  obtain ⟨y, rest, hy⟩ := List.exists_cons_of_ne_nil hdrop
  rw [← List.take_append_drop (Nat.clog 2 n) rng, hy, List.foldl_append, List.foldl_cons]
  have hpre := clogStep_foldl_lt (rng.take (Nat.clog 2 n)) 0 n (by omega)
  simp only [pow_zero, zero_add, htake] at hpre
  rw [hpre]
  dsimp only [clogStep]
  rw [if_neg (by decide : ¬ false = true), if_pos (Nat.le_pow_clog (by decide : 1 < 2) n)]
  have hdone : ∀ (zs : List ℕ) (k p m : ℕ), zs.foldl clogStep (true, k, p, m) = (true, k, p, m) := by
    intro zs k p m
    induction zs with
    | nil => rfl
    | cons _ _ ih => simpa [clogStep] using ih
  rw [hdone]

def bitsStep (st : ℕ × List Bool) (_ : ℕ) : ℕ × List Bool :=
  (st.1 / 2, decide (st.1 % 2 = 1) :: st.2)

def bitsLBounded (m K : ℕ) (rng : List ℕ) : List Bool :=
  ((rng.take K).foldl bitsStep (m, [])).2.reverse

lemma bitsStep_poly : Automatic.Poly (fun x : (ℕ × List Bool) × ℕ => bitsStep x.1 x.2) := by
  unfold bitsStep; fun_prop

lemma bitsStep_len (b : ℕ × List Bool) (g : ℕ) :
    (Coding.encode (bitsStep b g)).length ≤
      (Coding.encode b).length + 3 * (2 * (Coding.encode g).length + 1) := by
  have hd := NatBinary.length_mono (Nat.div_le_self b.1 2)
  have hbl : ∀ (c : Bool) (xs : List Bool),
      (encodeList (Coding.encode : Bool → List Bool) (c :: xs)).length =
        3 + (encodeList Coding.encode xs).length := by
    intro c xs
    rw [EncodedList.cons_length, enc_bool_eq]
    simp only [encodeBool, List.length_singleton]
  unfold bitsStep
  simp only [enc_pair_eq, enc_nat_eq, enc_list_eq, encodePair_length, hbl]
  omega

@[fun_prop] lemma bitsLBounded_comp {α : Type} [Coding α] {m K : α → ℕ} {rng : α → List ℕ}
    (hm : Automatic.Poly m) (hK : Automatic.Poly K) (hrng : Automatic.Poly rng) :
    Automatic.Poly (fun x => bitsLBounded (m x) (K x) (rng x)) := by
  unfold bitsLBounded
  have hfold : Automatic.Poly (fun x => ((rng x).take (K x)).foldl bitsStep (m x, [])) :=
    listFoldLinear_poly 0 3 bitsStep_poly bitsStep_len (by fun_prop) (by fun_prop)
  fun_prop

lemma bitsStep_foldl (zs : List ℕ) (m : ℕ) (acc : List Bool) :
    (zs.foldl bitsStep (m, acc)).2.reverse =
      acc.reverse ++ (List.range zs.length).map (fun j => m.testBit j) := by
  induction zs generalizing m acc with
  | nil => simp
  | cons _ zs ih =>
    simp only [List.foldl_cons, bitsStep, List.length_cons]
    rw [ih (m / 2) (decide (m % 2 = 1) :: acc), List.reverse_cons, List.append_assoc]
    congr 1
    rw [List.range_succ_eq_map, List.map_cons, List.singleton_append, List.map_map]
    congr 1
    · exact (Nat.testBit_zero m).symm
    · apply List.map_congr_left
      intro j _
      exact Nat.testBit_div_two m j

lemma bitsLBounded_getD (m K : ℕ) (rng : List ℕ) (hK : K ≤ rng.length) :
    ∀ j < K, (bitsLBounded m K rng)[j]?.getD false = m.testBit j := by
  intro j hj
  unfold bitsLBounded
  rw [bitsStep_foldl, List.reverse_nil, List.nil_append, List.length_take, Nat.min_eq_left hK]
  simp [hj]

lemma length_flatMap_const {α β : Type} (xs : List α) (ys : List β) :
    (xs.flatMap (fun _ => ys)).length = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons _ xs ih => simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]

def u1_30k (xs : List Bool) : List Unit := (true :: xs).map (fun _ => ())
def u2_30k (xs : List Bool) : List Unit := (u1_30k xs).flatMap (fun _ => u1_30k xs)
def u3_30k (xs : List Bool) : List Unit := (u2_30k xs).flatMap (fun _ => u1_30k xs)
def u10_30k : List Unit := List.replicate 10 ()
def u30_30k : List Unit := List.replicate 30 ()
def u100_30k : List Unit := u10_30k.flatMap (fun _ => u10_30k)
def u1000_30k : List Unit := u100_30k.flatMap (fun _ => u10_30k)
def u30000_30k : List Unit := u30_30k.flatMap (fun _ => u1000_30k)
def u30kCube (xs : List Bool) : List Unit := u30000_30k.flatMap (fun _ => u3_30k xs)
def range30kCube (xs : List Bool) : List ℕ := List.range (u30kCube xs).length

@[fun_prop] lemma range30kCube_poly : Automatic.Poly range30kCube := by
  unfold range30kCube u30kCube u3_30k u2_30k u1_30k
  fun_prop

lemma range30kCube_eq (xs : List Bool) :
    range30kCube xs = List.range (30000 * (xs.length + 1) ^ 3) := by
  unfold range30kCube u30kCube u3_30k u2_30k u1_30k u30000_30k u1000_30k u100_30k u30_30k u10_30k
  simp only [length_flatMap_const, List.length_replicate, List.length_map, List.length_cons]
  ring_nf

lemma take_range_eq (K N : ℕ) (h : K ≤ N) : (List.range N).take K = List.range K := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi1 hi2
    simp only [List.length_take, List.length_range, Nat.min_eq_left h] at hi1
    simp [List.getElem_range]

def encNatWithRange (rng : List ℕ) (n : ℕ) : List Bool :=
  (rng.take n).map (fun _ => true) ++ [false]

@[fun_prop] lemma encNatWithRange_comp {α : Type} [Coding α] {rng : α → List ℕ} {n : α → ℕ}
    (hrng : Automatic.Poly rng) (hn : Automatic.Poly n) :
    Automatic.Poly (fun x => encNatWithRange (rng x) (n x)) := by
  unfold encNatWithRange
  have hm : Automatic.Poly (fun x => ((rng x).take (n x)).map (fun _ => true)) :=
    Automatic.Poly.list_map (Automatic.Poly.const true) (list_take_comp hrng hn)
  fun_prop

lemma encNatWithRange_eq (N n : ℕ) (h : n ≤ N) :
    encNatWithRange (List.range N) n = encNat n := by
  unfold encNatWithRange QAlgorithms.Complexity.encNat
  rw [List.map_const', List.length_take, List.length_range, Nat.min_eq_left h]

def rawEncInstr (rng : List ℕ) (g : ℕ × ℕ × ℕ) : List Bool :=
  if g.1 = 4 then
    encNatWithRange rng g.1 ++ encNatWithRange rng g.2.1 ++ encNatWithRange rng g.2.2
  else
    encNatWithRange rng g.1 ++ encNatWithRange rng g.2.1

@[fun_prop] lemma rawEncInstr_comp {α : Type} [Coding α] {rng : α → List ℕ} {g : α → ℕ × ℕ × ℕ}
    (hrng : Automatic.Poly rng) (hg : Automatic.Poly g) :
    Automatic.Poly (fun x => rawEncInstr (rng x) (g x)) := by
  unfold rawEncInstr; fun_prop

lemma rawEncInstr_eq {n N : ℕ} (h4 : 4 ≤ N) (hn : n ≤ N) (g : Instr n) :
    rawEncInstr (List.range N) (rawOfInstr g) = encInstr g := by
  cases g with
  | h i =>
    have hi : i.val ≤ N := le_trans (Nat.le_of_lt i.isLt) hn
    simp only [rawOfInstr, rawEncInstr, QAlgorithms.Complexity.encInstr,
      if_neg (by decide : ¬ 0 = 4), encNatWithRange_eq N 0 (by omega), encNatWithRange_eq N i.val hi]
  | s i =>
    have hi : i.val ≤ N := le_trans (Nat.le_of_lt i.isLt) hn
    simp only [rawOfInstr, rawEncInstr, QAlgorithms.Complexity.encInstr,
      if_neg (by decide : ¬ 1 = 4), encNatWithRange_eq N 1 (by omega), encNatWithRange_eq N i.val hi]
  | t i =>
    have hi : i.val ≤ N := le_trans (Nat.le_of_lt i.isLt) hn
    simp only [rawOfInstr, rawEncInstr, QAlgorithms.Complexity.encInstr,
      if_neg (by decide : ¬ 2 = 4), encNatWithRange_eq N 2 (by omega), encNatWithRange_eq N i.val hi]
  | x i =>
    have hi : i.val ≤ N := le_trans (Nat.le_of_lt i.isLt) hn
    simp only [rawOfInstr, rawEncInstr, QAlgorithms.Complexity.encInstr,
      if_neg (by decide : ¬ 3 = 4), encNatWithRange_eq N 3 (by omega), encNatWithRange_eq N i.val hi]
  | cnot c t _ =>
    have hc : c.val ≤ N := le_trans (Nat.le_of_lt c.isLt) hn
    have ht : t.val ≤ N := le_trans (Nat.le_of_lt t.isLt) hn
    simp only [rawOfInstr, rawEncInstr, QAlgorithms.Complexity.encInstr,
      ↓reduceIte, encNatWithRange_eq N 4 h4, encNatWithRange_eq N c.val hc,
      encNatWithRange_eq N t.val ht]

def rawEncLayer (rng : List ℕ) (cs : List (ℕ × ℕ × ℕ)) : List Bool :=
  encNatWithRange rng cs.length ++ cs.flatMap (rawEncInstr rng)

@[fun_prop] lemma rawEncLayer_comp {α : Type} [Coding α] {rng : α → List ℕ}
    {cs : α → List (ℕ × ℕ × ℕ)} (hrng : Automatic.Poly rng) (hcs : Automatic.Poly cs) :
    Automatic.Poly (fun x => rawEncLayer (rng x) (cs x)) := by
  unfold rawEncLayer; fun_prop

lemma rawEncLayer_eq {n N : ℕ} (h4 : 4 ≤ N) (hn : n ≤ N) (cs : List (Instr n))
    (hcs : cs.length ≤ N) :
    rawEncLayer (List.range N) (cs.map rawOfInstr) = encLayer cs := by
  unfold rawEncLayer QAlgorithms.Complexity.encLayer QAlgorithms.Complexity.encStr
  rw [List.length_map, List.length_map, encNatWithRange_eq N cs.length hcs]
  congr 1
  rw [List.flatMap_def, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g _
  exact rawEncInstr_eq h4 hn g

@[fun_prop] lemma rawBase_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => rawBase (r x) (L x)) := by unfold rawBase; fun_prop
@[fun_prop] lemma rawW0_comp {α : Type} [Coding α] {r L : α → ℕ} :
    Automatic.Poly (fun x => rawW0 (r x) (L x)) := by unfold rawW0; fun_prop
@[fun_prop] lemma rawWW_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => rawWW (r x) (L x)) := by unfold rawWW; fun_prop
@[fun_prop] lemma rawWireF_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => rawWireF (r x) (L x)) := by unfold rawWireF; fun_prop
@[fun_prop] lemma rawZA_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => rawZA (r x) (L x)) := by unfold rawZA; fun_prop
@[fun_prop] lemma rawZB_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => rawZB (r x) (L x)) := by unfold rawZB; fun_prop

@[fun_prop] lemma specRegA_comp {α : Type} [Coding α] {r L : α → ℕ} (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specRegA (r x) (L x)) := by unfold specRegA; fun_prop
@[fun_prop] lemma specRegB_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specRegB (r x) (L x)) := by unfold specRegB; fun_prop
@[fun_prop] lemma specRegH_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specRegH (r x) (L x)) := by unfold specRegH; fun_prop
@[fun_prop] lemma specOut0_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specOut0 (r x) (L x)) := by unfold specOut0; fun_prop
@[fun_prop] lemma specOut1_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specOut1 (r x) (L x)) := by unfold specOut1; fun_prop
@[fun_prop] lemma specOut2_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specOut2 (r x) (L x)) := by unfold specOut2; fun_prop
@[fun_prop] lemma specOut3_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specOut3 (r x) (L x)) := by unfold specOut3; fun_prop
@[fun_prop] lemma specOut4_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specOut4 (r x) (L x)) := by unfold specOut4; fun_prop
@[fun_prop] lemma specOutAll_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specOutAll (r x) (L x)) := by unfold specOutAll; fun_prop
@[fun_prop] lemma specLowAll_comp {α : Type} [Coding α] {r L : α → ℕ} (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specLowAll (r x) (L x)) := by unfold specLowAll; fun_prop
@[fun_prop] lemma specTmp_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specTmp (r x) (L x)) := by unfold specTmp; fun_prop
@[fun_prop] lemma specRegM_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specRegM (r x) (L x)) := by unfold specRegM; fun_prop
@[fun_prop] lemma specRegS_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specRegS (r x) (L x)) := by unfold specRegS; fun_prop
@[fun_prop] lemma specRegC_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specRegC (r x) (L x)) := by unfold specRegC; fun_prop
@[fun_prop] lemma specRegD1_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specRegD1 (r x) (L x)) := by unfold specRegD1; fun_prop
@[fun_prop] lemma specRegBr1_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specRegBr1 (r x) (L x)) := by unfold specRegBr1; fun_prop
@[fun_prop] lemma specRegD2_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specRegD2 (r x) (L x)) := by unfold specRegD2; fun_prop
@[fun_prop] lemma specRegBr2_comp {α : Type} [Coding α] {r L : α → ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) :
    Automatic.Poly (fun x => specRegBr2 (r x) (L x)) := by unfold specRegBr2; fun_prop
@[fun_prop] lemma specLift_comp {α : Type} [Coding α] {s : α → RegSpec} {z : α → ℕ}
    (hs : Automatic.Poly s) (hz : Automatic.Poly z) :
    Automatic.Poly (fun x => specLift (s x) (z x)) := by unfold specLift; fun_prop

@[fun_prop] lemma evalReg_comp {α : Type} [Coding α] {s : α → RegSpec} {j : α → ℕ}
    (hs : Automatic.Poly s) (hj : Automatic.Poly j) :
    Automatic.Poly (fun x => evalReg (s x) (j x)) := by unfold evalReg; fun_prop

@[fun_prop] lemma rawCCX_comp {α : Type} [Coding α] {a b t : α → ℕ}
    (ha : Automatic.Poly a) (hb : Automatic.Poly b) (ht : Automatic.Poly t) :
    Automatic.Poly (fun x => rawCCX (a x) (b x) (t x)) := by
  unfold rawCCX
  dsimp only
  apply Automatic.Poly.list_map _ (Automatic.Poly.const ccx3Raw)
  fun_prop

@[fun_prop] lemma rawCompileRevGate_comp {α : Type} [Coding α] {g : α → ℕ × ℕ × ℕ × ℕ}
    (hg : Automatic.Poly g) :
    Automatic.Poly (fun x => rawCompileRevGate (g x)) := by
  unfold rawCompileRevGate; fun_prop

@[fun_prop] lemma rawCompileRev_comp {α : Type} [Coding α] {cs : α → List (ℕ × ℕ × ℕ × ℕ)}
    (hcs : Automatic.Poly cs) :
    Automatic.Poly (fun x => rawCompileRev (cs x)) := by
  unfold rawCompileRev; fun_prop

@[fun_prop] lemma rawInitNat_comp {α : Type} [Coding α] {bitsM : α → List Bool}
    {sX : α → RegSpec} {rng : α → List ℕ}
    (hb : Automatic.Poly bitsM) (hs : Automatic.Poly sX) (hrng : Automatic.Poly rng) :
    Automatic.Poly (fun x => rawInitNat (bitsM x) (sX x) (rng x)) := by
  unfold rawInitNat; fun_prop

@[fun_prop] lemma rawCCXLoop_comp {α : Type} [Coding α] {ctrl : α → ℕ}
    {sSrc sDst : α → RegSpec} {rng : α → List ℕ}
    (hc : Automatic.Poly ctrl) (hs : Automatic.Poly sSrc) (hd : Automatic.Poly sDst)
    (hrng : Automatic.Poly rng) :
    Automatic.Poly (fun x => rawCCXLoop (ctrl x) (sSrc x) (sDst x) (rng x)) := by
  unfold rawCCXLoop; fun_prop

@[fun_prop] lemma rawSwapLoop_comp {α : Type} [Coding α] {sA sB : α → RegSpec}
    {rng : α → List ℕ}
    (ha : Automatic.Poly sA) (hb : Automatic.Poly sB) (hrng : Automatic.Poly rng) :
    Automatic.Poly (fun x => rawSwapLoop (sA x) (sB x) (rng x)) := by
  unfold rawSwapLoop; fun_prop

@[fun_prop] lemma rawRippleAdd_comp {α : Type} [Coding α] {sA sB sS sC : α → RegSpec}
    {rng : α → List ℕ}
    (ha : Automatic.Poly sA) (hb : Automatic.Poly sB) (hs : Automatic.Poly sS)
    (hc : Automatic.Poly sC) (hrng : Automatic.Poly rng) :
    Automatic.Poly (fun x => rawRippleAdd (sA x) (sB x) (sS x) (sC x) (rng x)) := by
  unfold rawRippleAdd; fun_prop

@[fun_prop] lemma rawRippleSub_comp {α : Type} [Coding α] {sX sY sD sBr : α → RegSpec}
    {rng : α → List ℕ}
    (hx : Automatic.Poly sX) (hy : Automatic.Poly sY) (hd : Automatic.Poly sD)
    (hbr : Automatic.Poly sBr) (hrng : Automatic.Poly rng) :
    Automatic.Poly (fun x => rawRippleSub (sX x) (sY x) (sD x) (sBr x) (rng x)) := by
  unfold rawRippleSub; fun_prop

@[fun_prop] lemma rawAddModMPre_comp {α : Type} [Coding α] {r L : α → ℕ}
    {bitsM : α → List Bool} {sX sY : α → RegSpec} {rngL1 : α → List ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) (hb : Automatic.Poly bitsM)
    (hx : Automatic.Poly sX) (hy : Automatic.Poly sY) (hrng : Automatic.Poly rngL1) :
    Automatic.Poly (fun x => rawAddModMPre (r x) (L x) (bitsM x) (sX x) (sY x) (rngL1 x)) := by
  unfold rawAddModMPre; fun_prop

@[fun_prop] lemma rawAddModMCopy_comp {α : Type} [Coding α] {r L : α → ℕ}
    {sOut : α → RegSpec} {rngL : α → List ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) (ho : Automatic.Poly sOut)
    (hrng : Automatic.Poly rngL) :
    Automatic.Poly (fun x => rawAddModMCopy (r x) (L x) (sOut x) (rngL x)) := by
  unfold rawAddModMCopy; fun_prop

@[fun_prop] lemma rawAddModM_comp {α : Type} [Coding α] {r L : α → ℕ}
    {bitsM : α → List Bool} {sX sY sOut : α → RegSpec} {rngL rngL1 : α → List ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) (hb : Automatic.Poly bitsM)
    (hx : Automatic.Poly sX) (hy : Automatic.Poly sY) (ho : Automatic.Poly sOut)
    (hrng : Automatic.Poly rngL) (hrng1 : Automatic.Poly rngL1) :
    Automatic.Poly (fun x => rawAddModM (r x) (L x) (bitsM x) (sX x) (sY x) (sOut x) (rngL x) (rngL1 x)) := by
  unfold rawAddModM; dsimp only; fun_prop

@[fun_prop] lemma rawSubModMPre_comp {α : Type} [Coding α] {r L : α → ℕ}
    {bitsM : α → List Bool} {sX sY : α → RegSpec} {rngL1 : α → List ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) (hb : Automatic.Poly bitsM)
    (hx : Automatic.Poly sX) (hy : Automatic.Poly sY) (hrng : Automatic.Poly rngL1) :
    Automatic.Poly (fun x => rawSubModMPre (r x) (L x) (bitsM x) (sX x) (sY x) (rngL1 x)) := by
  unfold rawSubModMPre; fun_prop

@[fun_prop] lemma rawSubModMCopy_comp {α : Type} [Coding α] {r L : α → ℕ}
    {sOut : α → RegSpec} {rngL : α → List ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) (ho : Automatic.Poly sOut)
    (hrng : Automatic.Poly rngL) :
    Automatic.Poly (fun x => rawSubModMCopy (r x) (L x) (sOut x) (rngL x)) := by
  unfold rawSubModMCopy; fun_prop

@[fun_prop] lemma rawSubModM_comp {α : Type} [Coding α] {r L : α → ℕ}
    {bitsM : α → List Bool} {sX sY sOut : α → RegSpec} {rngL rngL1 : α → List ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) (hb : Automatic.Poly bitsM)
    (hx : Automatic.Poly sX) (hy : Automatic.Poly sY) (ho : Automatic.Poly sOut)
    (hrng : Automatic.Poly rngL) (hrng1 : Automatic.Poly rngL1) :
    Automatic.Poly (fun x => rawSubModM (r x) (L x) (bitsM x) (sX x) (sY x) (sOut x) (rngL x) (rngL1 x)) := by
  unfold rawSubModM; dsimp only; fun_prop

@[fun_prop] lemma rawFbOutCCU_comp {α : Type} [Coding α]
    {pre : α → List (ℕ × ℕ × ℕ × ℕ)} {ctrl : α → ℕ}
    {sSrc sDst : α → RegSpec} {rngL : α → List ℕ}
    (hp : Automatic.Poly pre) (hc : Automatic.Poly ctrl) (hs : Automatic.Poly sSrc)
    (hd : Automatic.Poly sDst) (hrng : Automatic.Poly rngL) :
    Automatic.Poly (fun x => rawFbOutCCU (pre x) (ctrl x) (sSrc x) (sDst x) (rngL x)) := by
  unfold rawFbOutCCU; fun_prop

@[fun_prop] lemma rawFbOutFwd_comp {α : Type} [Coding α] {r L : α → ℕ}
    {bitsM : α → List Bool} {rngL rngL1 : α → List ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) (hb : Automatic.Poly bitsM)
    (hrng : Automatic.Poly rngL) (hrng1 : Automatic.Poly rngL1) :
    Automatic.Poly (fun x => rawFbOutFwd (r x) (L x) (bitsM x) (rngL x) (rngL1 x)) := by
  unfold rawFbOutFwd; dsimp only; fun_prop

@[fun_prop] lemma rawFbOutUnc_comp {α : Type} [Coding α] {r L : α → ℕ}
    {bitsM : α → List Bool} {rngL rngL1 : α → List ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) (hb : Automatic.Poly bitsM)
    (hrng : Automatic.Poly rngL) (hrng1 : Automatic.Poly rngL1) :
    Automatic.Poly (fun x => rawFbOutUnc (r x) (L x) (bitsM x) (rngL x) (rngL1 x)) := by
  unfold rawFbOutUnc; dsimp only; fun_prop

@[fun_prop] lemma rawFbOutSwap_comp {α : Type} [Coding α] {r L : α → ℕ}
    {rng5L : α → List ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) (hrng : Automatic.Poly rng5L) :
    Automatic.Poly (fun x => rawFbOutSwap (r x) (L x) (rng5L x)) := by
  unfold rawFbOutSwap; fun_prop

@[fun_prop] lemma rawFbOutRev_comp {α : Type} [Coding α] {r L : α → ℕ}
    {bitsM : α → List Bool} {rngL rngL1 rng5L : α → List ℕ}
    (hr : Automatic.Poly r) (hL : Automatic.Poly L) (hb : Automatic.Poly bitsM)
    (hrng : Automatic.Poly rngL) (hrng1 : Automatic.Poly rngL1) (hrng5 : Automatic.Poly rng5L) :
    Automatic.Poly (fun x => rawFbOutRev (r x) (L x) (bitsM x) (rngL x) (rngL1 x) (rng5L x)) := by
  unfold rawFbOutRev; fun_prop

lemma encBin_length (m : ℕ) :
    (QAlgorithms.LocalHamiltonian.encBin m).length = 2 * m.bits.length + 2 := by
  unfold QAlgorithms.LocalHamiltonian.encBin
  rw [List.length_append, List.length_flatMap]
  have hs : (m.bits.map (fun β => ([true, β] : List Bool).length)).sum = 2 * m.bits.length := by
    have hmap : m.bits.map (fun β => ([true, β] : List Bool).length) = List.replicate m.bits.length 2 := by
      simp [List.map_const']
    rw [hmap, List.sum_replicate, smul_eq_mul, mul_comm]
  rw [hs]
  rfl

lemma encData_bounds (D : FieldData) (k : ℕ) :
    let n := (D.encData ++ QAlgorithms.Complexity.encNat k).length
    D.p.bits.length ≤ n ∧ D.r + 1 ≤ n ∧ D.q ^ 2 ≤ 2 ^ (2 * n ^ 2) ∧
      D.labW ≤ 2 * n ^ 2 ∧
      fbOutW_raw D.r D.labW ≤ 30000 * (n + 1) ^ 3 ∧
      (fbOutCirc D).length ≤ 30000 * (n + 1) ^ 3 := by
  intro n
  have henc : D.encData.length ≤ n := by simp [n]
  have hp_le : 2 * D.p.bits.length + 2 ≤ D.encData.length := by
    unfold GL2QFT.FieldData.encData
    simp only [List.length_append, ← encBin_length D.p]
    omega
  have hp_bits : D.p.bits.length ≤ n := by omega
  have hr_piece : 2 * (D.r + 1) ≤
      ((List.range (D.r + 1)).flatMap fun j =>
        QAlgorithms.LocalHamiltonian.encBin (D.f.coeff j).val).length := by
    rw [List.length_flatMap]
    have hge2 : ∀ j ∈ List.range (D.r + 1),
        2 ≤ (QAlgorithms.LocalHamiltonian.encBin (D.f.coeff j).val).length := by
      intro j _; rw [encBin_length]; omega
    have hsum := List.sum_le_sum (fun j hj => hge2 j hj)
    have hlen : (List.map (fun _ => 2) (List.range (D.r + 1))).sum = 2 * (D.r + 1) := by
      rw [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul, mul_comm]
    simpa [Function.comp_def, hlen, mul_comm] using hsum
  have hr_enc : 2 * (D.r + 1) ≤ D.encData.length := by
    unfold GL2QFT.FieldData.encData
    simp only [List.length_append]
    omega
  have hr1_le : D.r + 1 ≤ n := by omega
  have hp2 : D.p ≤ 2 ^ D.p.bits.length := NatBinary.le_two_pow_length D.p
  have hq_le : D.q ≤ 2 ^ (n ^ 2) := by
    change D.p ^ D.r ≤ 2 ^ (n ^ 2)
    have h1 : D.p ^ D.r ≤ (2 ^ D.p.bits.length) ^ D.r := Nat.pow_le_pow_left hp2 D.r
    have h2 : (2 ^ D.p.bits.length) ^ D.r = 2 ^ (D.p.bits.length * D.r) := (Nat.pow_mul 2 _ _).symm
    have hmul : D.p.bits.length * D.r ≤ n ^ 2 := by nlinarith
    have h3 : 2 ^ (D.p.bits.length * D.r) ≤ 2 ^ (n ^ 2) := Nat.pow_le_pow_right (by omega) hmul
    omega
  have hq2_le : D.q ^ 2 ≤ 2 ^ (2 * n ^ 2) := by
    have h1 : D.q ^ 2 ≤ (2 ^ (n ^ 2)) ^ 2 := Nat.pow_le_pow_left hq_le 2
    have h2 : (2 ^ (n ^ 2)) ^ 2 = 2 ^ (2 * n ^ 2) := by rw [← Nat.pow_mul, mul_comm]
    omega
  have hlabW : D.labW ≤ 2 * n ^ 2 :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hq2_le
  have hW_le : fbOutW_raw D.r D.labW ≤ 30000 * (n + 1) ^ 3 := by
    unfold fbOutW_raw
    nlinarith
  have hC_le : (fbOutCirc D).length ≤ 30000 * (n + 1) ^ 3 := by
    have h1 : (fbOutCirc D).length ≤ 24 * (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D)).length := by
      unfold fbOutCirc
      exact compileRev_length_le _
    have h2 := fbOutRev_length D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D)
    nlinarith
  exact ⟨hp_bits, hr1_le, hq2_le, hlabW, hW_le, hC_le⟩

def f_fbOut (xs : List Bool) : List Bool :=
  let pr := parsePR xs
  let rng := range30kCube xs
  let q := powBounded pr.1 pr.2 rng
  let L := clog2Bounded (q * q) rng
  let bitsM := bitsLBounded (q - 1) (L + 1) rng
  let fbW := 3 * ((pr.2 + 1) * L) + 13 * L + 12
  let rev := rawFbOutRev pr.2 L bitsM (rng.take L) (rng.take (L + 1)) (rng.take (5 * L))
  encNatWithRange rng fbW ++ rawEncLayer rng (rawCompileRev rev)

lemma f_fbOut_poly : Automatic.Poly f_fbOut := by
  unfold f_fbOut
  dsimp only
  fun_prop

lemma f_fbOut_polyTime : PolyTimeComputable f_fbOut :=
  polyProgram_id_of_poly f_fbOut_poly

lemma f_fbOut_eq (D : FieldData) (k : ℕ) :
    f_fbOut (D.encData ++ encNat k) =
      encNat (fbOutW_raw D.r D.labW) ++ encLayer (fbOutCirc D) := by
  let xs := D.encData ++ encNat k
  let N := 30000 * (xs.length + 1) ^ 3
  obtain ⟨_, hr1_le, _, hlabW, hW_le, hC_le⟩ := encData_bounds D k
  have hrng : range30kCube xs = List.range N := range30kCube_eq xs
  have hrng_len : (range30kCube xs).length = N := by rw [hrng, List.length_range]
  have hpr : parsePR xs = (D.p, D.r) := parsePR_encData D (encNat k)
  have hr_N : D.r ≤ N := by dsimp [N]; nlinarith
  have hq : powBounded D.p D.r (range30kCube xs) = D.q := by
    rw [powBounded_eq D.p D.r _ (by rw [hrng_len]; exact hr_N)]; rfl
  have hqq : D.q * D.q = D.q ^ 2 := (sq D.q).symm
  have hL_N : D.labW + 1 ≤ N := by dsimp [N]; nlinarith
  have hL : clog2Bounded (D.q * D.q) (range30kCube xs) = D.labW := by
    rw [hqq]
    exact clog2Bounded_eq (D.q ^ 2) _ (by rw [hrng_len]; exact hL_N)
  have h4_N : 4 ≤ N := by dsimp [N]; nlinarith
  have h5L_N : 5 * D.labW ≤ N := by dsimp [N]; nlinarith
  have hb : ∀ j < D.labW + 1,
      (bitsLBounded (D.q - 1) (D.labW + 1) (range30kCube xs))[j]?.getD false = (D.q - 1).testBit j :=
    bitsLBounded_getD (D.q - 1) (D.labW + 1) _ (by rw [hrng_len]; exact hL_N)
  have htL : (range30kCube xs).take D.labW = List.range D.labW := by
    rw [hrng]; exact take_range_eq D.labW N (by omega)
  have htL1 : (range30kCube xs).take (D.labW + 1) = List.range (D.labW + 1) := by
    rw [hrng]; exact take_range_eq (D.labW + 1) N hL_N
  have ht5L : (range30kCube xs).take (5 * D.labW) = List.range (5 * D.labW) := by
    rw [hrng]; exact take_range_eq (5 * D.labW) N h5L_N
  have hrev := rawFbOutRev_eq D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D)
    (bitsLBounded (D.q - 1) (D.labW + 1) (range30kCube xs)) hb
  unfold f_fbOut
  dsimp only
  change encNatWithRange (range30kCube xs)
      (3 * (((parsePR xs).2 + 1) * clog2Bounded (powBounded (parsePR xs).1 (parsePR xs).2 (range30kCube xs) *
        powBounded (parsePR xs).1 (parsePR xs).2 (range30kCube xs)) (range30kCube xs)) +
        13 * clog2Bounded (powBounded (parsePR xs).1 (parsePR xs).2 (range30kCube xs) *
        powBounded (parsePR xs).1 (parsePR xs).2 (range30kCube xs)) (range30kCube xs) + 12) ++
    rawEncLayer (range30kCube xs) (rawCompileRev (rawFbOutRev (parsePR xs).2
      (clog2Bounded (powBounded (parsePR xs).1 (parsePR xs).2 (range30kCube xs) *
        powBounded (parsePR xs).1 (parsePR xs).2 (range30kCube xs)) (range30kCube xs))
      (bitsLBounded (powBounded (parsePR xs).1 (parsePR xs).2 (range30kCube xs) - 1)
        (clog2Bounded (powBounded (parsePR xs).1 (parsePR xs).2 (range30kCube xs) *
          powBounded (parsePR xs).1 (parsePR xs).2 (range30kCube xs)) (range30kCube xs) + 1)
        (range30kCube xs))
      ((range30kCube xs).take _) ((range30kCube xs).take _) ((range30kCube xs).take _))) =
    encNat (fbOutW_raw D.r D.labW) ++ encLayer (fbOutCirc D)
  rw [hpr, hq, hL, htL, htL1, ht5L, ← hrev, ← rawCompileRev_eq]
  change encNatWithRange (range30kCube xs) (fbOutW_raw D.r D.labW) ++
      rawEncLayer (range30kCube xs) ((fbOutCirc D).map rawOfInstr) =
    encNat (fbOutW_raw D.r D.labW) ++ encLayer (fbOutCirc D)
  rw [hrng, encNatWithRange_eq N (fbOutW_raw D.r D.labW) hW_le,
    rawEncLayer_eq h4_N hW_le (fbOutCirc D) hC_le]

lemma fbOutCirc_length_le (D : FieldData) (k : ℕ) :
    (fbOutCirc D).length ≤ 16 * (Nat.log 2 D.q + k + 2) ^ 16 := by
  have hlog : D.q < 2 ^ (Nat.log 2 D.q + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) D.q
  have hsq : D.q ^ 2 ≤ 2 ^ (2 * Nat.log 2 D.q + 2) := by
    have h1 : D.q ^ 2 ≤ (2 ^ (Nat.log 2 D.q + 1)) ^ 2 := Nat.pow_le_pow_left hlog.le 2
    have h2 : (2 ^ (Nat.log 2 D.q + 1)) ^ 2 = 2 ^ (2 * Nat.log 2 D.q + 2) := by
      rw [← Nat.pow_mul]; ring_nf
    omega
  have hlabW : D.labW ≤ 2 * Nat.log 2 D.q + 2 :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hsq
  have h1 : (fbOutCirc D).length ≤ 24 * (fbOutRev D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D)).length := by
    unfold fbOutCirc; exact compileRev_length_le _
  have h2 := fbOutRev_length D.r (D.q - 1) D.labW D.hr (fd_one_le_labW D)
  have hlin : (fbOutCirc D).length ≤ 24000 * (Nat.log 2 D.q + k + 2) := by omega
  have hpow15 : 2 ^ 15 ≤ (Nat.log 2 D.q + k + 2) ^ 15 := Nat.pow_le_pow_left (by omega) 15
  have hc : 24000 ≤ 16 * 2 ^ 15 := by decide
  have h16 : (Nat.log 2 D.q + k + 2) ^ 16 = (Nat.log 2 D.q + k + 2) * (Nat.log 2 D.q + k + 2) ^ 15 := by
    ring
  nlinarith

end Section4_Poly

end GL2QFT_FBOut_Aux

theorem solution :
    GL2QFT.UniformlyImplementsOn (fun _ => True)
      (fun D => GL2QFT.Circuits.bMidCode D)
      (fun D => D.bOutCode)
      (fun D => GL2QFT.Circuits.permMat (GL2QFT.Circuits.fbOutPerm D)) := by
  refine ⟨fun D _ => GL2QFT_FBOut_Aux.fbOutW_raw D.r D.labW,
    fun D _ => GL2QFT_FBOut_Aux.fbOutCirc D,
    GL2QFT_FBOut_Aux.f_fbOut, 16,
    GL2QFT_FBOut_Aux.f_fbOut_polyTime, ?_, ?_, ?_⟩
  · intro D _ k
    exact GL2QFT_FBOut_Aux.f_fbOut_eq D k
  · intro D _ k
    exact GL2QFT_FBOut_Aux.fbOutCirc_length_le D k
  · intro D _ k
    refine ⟨?_, ?_, GL2QFT_FBOut_Aux.fbOutCirc_implements D k⟩
    · simp only [GL2QFT_FBOut_Aux.fbOutW_raw]; omega
    · have h5 := GL2QFT_FBOut_Aux.five_L_le_three_W D.r D.labW D.hr
      simp only [GL2QFT_FBOut_Aux.fbOutW_raw]; omega
