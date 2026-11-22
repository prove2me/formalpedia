-- Prove2me | solution 1 for GL2QFT.Circuits.totalA_split_merge_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T07:58:51.920864+00:00
-- url     : https://prove2.me/submissions/3b1ff7f8-9185-4180-9915-c94a5c3759e7

import Definitions.Def_GL2QFT_Circuits_Leaves
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

set_option autoImplicit false

noncomputable section

open Classical

namespace GL2QFT_TotalASplitMerge_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.Supplement GL2QFT.Supplement.TotalA
  QAlgorithms QAlgorithms.Complexity QAlgorithms.LocalHamiltonian
open OAI.MetricKMedian.Binary
open Automatic

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

lemma act_sum {ι α : Type} [Fintype ι] (M : Matrix ι ι ℂ) (s : Finset α)
    (v : α → EuclideanSpace ℂ ι) :
    act M (∑ a ∈ s, v a) = ∑ a ∈ s, act M (v a) := by
  induction s using Finset.induction_on with
  | empty =>
    apply WithLp.ofLp_injective
    funext y
    simp [act, Matrix.mulVec_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

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

lemma circUnitary_nil {n : ℕ} : circUnitary ([] : List (Instr n)) = 1 := by
  simp [circUnitary, Circuit.unitary]

lemma circUnitary_append {n : ℕ} (c₁ c₂ : List (Instr n)) :
    circUnitary (c₁ ++ c₂) = circUnitary c₂ * circUnitary c₁ := by
  simp [circUnitary, Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma embedOp_one {k n : ℕ} (w : Fin k ↪ Fin n) :
    embedOp (1 : Matrix (Qubits k) (Qubits k) ℂ) w = 1 := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso; apply hyz; funext a
      by_cases ha : ∃ i, w i = a
      · rcases ha with ⟨i, rfl⟩; exact congrFun h2 i
      · exact h1 a (fun ⟨i, hi⟩ => ha ⟨i, hi⟩)
    · rfl
    · rfl

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
  · rw [if_pos (hiff.mpr h), if_pos h]; rfl
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
  · rw [if_pos (hiff.mpr h), if_pos h]; rfl
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
      · exfalso; apply hy; funext a
        by_cases hai : a = i
        · subst hai; cases hza : z a <;> cases hya : y a <;> simp_all
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
      · exfalso; apply hy; funext a
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
  · subst hyz; rw [if_pos rfl, if_pos (fun _ _ => rfl), if_pos rfl]
  · rw [if_neg hyz]
    by_cases h1 : ∀ a : Fin n, a ≠ i → y a = z a
    · rw [if_pos h1]
      have hne : y i ≠ z i := by
        intro heq; apply hyz; funext a
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
  · subst hyz; rw [if_pos rfl, if_pos (fun _ _ => rfl), if_pos rfl]
  · rw [if_neg hyz]
    by_cases h1 : ∀ a : Fin n, a ≠ i → y a = z a
    · rw [if_pos h1]
      have hne : y i ≠ z i := by
        intro heq; apply hyz; funext a
        by_cases hai : a = i
        · subst hai; exact heq
        · exact h1 a hai
      rw [if_neg hne]
    · rw [if_neg h1]

lemma act_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (q : ι) :
    act (Matrix.diagonal d) (ket q) = d q • ket q := by
  apply WithLp.ofLp_injective
  funext y
  by_cases hy : y = q
  · subst hy; simp [act_ket, ket_apply]
  · simp [act_ket, ket_apply, hy]

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
  simpa using congrArg (fun r : ℝ => (r : ℂ)) hr

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
      · rcases hex with ⟨i, rfl⟩; exact hmkU_w (fun i => u (w i)) i
      · simp only [mkU, dif_neg hex]; exact hu a (fun ⟨i, hi⟩ => hex ⟨i, hi⟩)
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
      ext a; fin_cases a
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

/-! ### Section 2: Reversible gate layer (`RevGate`) and shift-up combinator -/

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

@[simp] lemma evalRev_nil {n : ℕ} (q : Qubits n) : evalRev [] q = q := rfl

@[simp] lemma evalRev_cons {n : ℕ} (g : RevGate n) (gs : List (RevGate n)) (q : Qubits n) :
    evalRev (g :: gs) q = evalRev gs (g.eval q) := rfl

@[simp] lemma evalRev_append {n : ℕ} (gs₁ gs₂ : List (RevGate n)) (q : Qubits n) :
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
    dsimp [RevGate.compile, RevGate.eval]
    rw [circUnitary_mapCirc, circUnitary_ccx3, embedOp_wire3_ccx]
    rfl

lemma circUnitary_compileRev {n : ℕ} (gs : List (RevGate n)) :
    circUnitary (compileRev gs) = permMat (evalRev gs) := by
  induction gs with
  | nil =>
    ext y z
    by_cases h : y = z <;>
      simp [compileRev, evalRev, circUnitary_nil, permMat, Matrix.one_apply, h]
  | cons g gs ih =>
    have hcons : g :: gs = [g] ++ gs := rfl
    rw [hcons, compileRev_append, circUnitary_append, ih]
    have hg : compileRev [g] = g.compile := List.append_nil _
    rw [hg, circUnitary_compile, permMat_mul]
    rfl

lemma compileRev_length_le {n : ℕ} (gs : List (RevGate n)) :
    (compileRev gs).length ≤ 25 * gs.length := by
  induction gs with
  | nil => simp [compileRev]
  | cons g gs ih =>
    have hg : g.compile.length ≤ 25 := by
      cases g with
      | x i => simp [RevGate.compile]
      | cnot i j hij => simp [RevGate.compile]
      | ccx i j k hij hik hjk =>
        change (mapCirc (wire3 i j k hij hik hjk) ccx3).length ≤ 25
        change (ccx3.map (mapInstr (wire3 i j k hij hik hjk))).length ≤ 25
        rw [List.length_map]
        decide
    simp only [compileRev, List.flatMap_cons, List.length_append, List.length_cons]
    have ih' : (compileRev gs).length ≤ 25 * gs.length := ih
    unfold compileRev at ih'
    omega

lemma ofLp_sum {ι α : Type} [Fintype ι] (s : Finset α) (f : α → EuclideanSpace ℂ ι) :
    (∑ a ∈ s, f a).ofLp = ∑ a ∈ s, (f a).ofLp := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

lemma implements_of_act_ket_perm {X Y : Type} [Fintype X] [Fintype Y] {n : ℕ}
    (U : Matrix (Qubits n) (Qubits n) ℂ) (cin : X → Qubits n) (cout : Y → Qubits n)
    (f : X → Y) (h : ∀ x : X, act U (ket (cin x)) = ket (cout (f x))) (ε : ℝ) (hε : 0 ≤ ε) :
    Implements U cin cout (permMat f) ε := by
  intro ψ
  have hembed_in : embedVec cin ψ = ∑ x : X, ψ x • ket (cin x) := by
    apply WithLp.ofLp_injective
    funext q
    rw [ofLp_sum, Finset.sum_apply]
    simp only [embedVec, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul, ket_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : cin x = q
    · simp [hx]
    · simp [hx, Ne.symm hx]
  have hembed_out : embedVec cout (WithLp.toLp 2 ((permMat f).mulVec (WithLp.ofLp ψ))) =
      ∑ x : X, ψ x • ket (cout (f x)) := by
    apply WithLp.ofLp_injective
    funext q
    rw [ofLp_sum, Finset.sum_apply]
    simp only [embedVec, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul, ket_apply,
      Matrix.mulVec, dotProduct, permMat, Matrix.of_apply]
    calc (∑ y : Y, if cout y = q then ∑ x : X, (if y = f x then (1 : ℂ) else 0) * ψ x else 0)
        = ∑ y : Y, ∑ x : X, (if cout y = q then if y = f x then ψ x else 0 else 0) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            split_ifs with hy
            · refine Finset.sum_congr rfl fun x _ => ?_
              split_ifs <;> simp
            · simp
      _ = ∑ x : X, ∑ y : Y, (if y = f x then if cout y = q then ψ x else 0 else 0) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
            by_cases h1 : cout y = q <;> by_cases h2 : y = f x <;> simp [h1, h2]
      _ = ∑ x : X, if cout (f x) = q then ψ x else 0 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_eq_single (f x)]
            · simp
            · intro y _ hy; simp [hy]
            · intro hm; exact absurd (Finset.mem_univ (f x)) hm
      _ = ∑ x : X, ψ x * (if q = cout (f x) then 1 else 0) := by
            refine Finset.sum_congr rfl fun x _ => by
              by_cases hq : q = cout (f x) <;> simp [hq, eq_comm]
  have hact : act U (embedVec cin ψ) =
      embedVec cout (WithLp.toLp 2 ((permMat f).mulVec (WithLp.ofLp ψ))) := by
    rw [hembed_in, hembed_out, act_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [act_smul, h x]
  rw [hact, sub_self, norm_zero]
  exact mul_nonneg hε (norm_nonneg ψ)

def swapRev {n : ℕ} (a b : Fin n) (hab : a ≠ b) : List (RevGate n) :=
  [.cnot a b hab, .cnot b a hab.symm, .cnot a b hab]

@[simp]
lemma evalRev_swapRev {n : ℕ} (a b : Fin n) (hab : a ≠ b) (q : Qubits n) :
    evalRev (swapRev a b hab) q = fun i => if i = a then q b else if i = b then q a else q i := by
  simp only [swapRev, evalRev_cons, evalRev_nil, RevGate.eval]
  funext i
  by_cases ha : i = a
  · subst ha
    simp only [Function.update_apply, hab, hab.symm, ↓reduceIte]
    cases q i <;> cases q b <;> rfl
  · by_cases hb : i = b
    · subst hb
      simp only [Function.update_apply, ha, Ne.symm ha, ↓reduceIte]
      cases q a <;> cases q i <;> rfl
    · simp [ha, hb]

def shiftUpAux {W N : ℕ} (hWN : W < N) : (k : ℕ) → k ≤ W → List (RevGate N)
  | 0, _ => []
  | k + 1, hk =>
      swapRev ⟨k, by omega⟩ ⟨k + 1, by omega⟩ (by simp [Fin.ext_iff]) ++
        shiftUpAux hWN k (by omega)

lemma shiftUpAux_length {W N : ℕ} (hWN : W < N) (k : ℕ) (hk : k ≤ W) :
    (shiftUpAux hWN k hk).length = 3 * k := by
  induction k with
  | zero => simp [shiftUpAux]
  | succ k ih =>
    simp [shiftUpAux, swapRev, ih (by omega)]
    omega

lemma evalRev_shiftUpAux {W N : ℕ} (hWN : W < N) (k : ℕ) (hk : k ≤ W) (q : Qubits N) :
    evalRev (shiftUpAux hWN k hk) q = fun i : Fin N =>
      if i.val = 0 then q ⟨k, by omega⟩
      else if i.val ≤ k then q ⟨i.val - 1, by omega⟩
      else q i := by
  induction k generalizing q with
  | zero =>
    simp only [shiftUpAux, evalRev_nil]
    funext i
    split_ifs with h0 hle
    · congr 1; exact Fin.ext h0
    · omega
    · rfl
  | succ k ih =>
    simp only [shiftUpAux, evalRev_append, evalRev_swapRev]
    rw [ih (by omega)]
    funext i
    by_cases hi0 : i.val = 0
    · simp [hi0]
    · by_cases hik : i.val ≤ k + 1
      · simp only [hi0, ↓reduceIte, hik]
        by_cases hle : i.val ≤ k
        · simp only [hle, ↓reduceIte]
          have hne1 : (⟨i.val - 1, by omega⟩ : Fin N) ≠ ⟨k, by omega⟩ := by
            simp [Fin.ext_iff]; omega
          have hne2 : (⟨i.val - 1, by omega⟩ : Fin N) ≠ ⟨k + 1, by omega⟩ := by
            simp [Fin.ext_iff]; omega
          simp [hne1, hne2]
        · have hik_eq : i.val = k + 1 := by omega
          have hne0 : ¬ (i.val ≤ k) := hle
          simp only [hne0, ↓reduceIte]
          have heqi : i = ⟨k + 1, by omega⟩ := Fin.ext hik_eq
          have hne : (⟨k + 1, by omega⟩ : Fin N) ≠ ⟨k, by omega⟩ := by simp [Fin.ext_iff]
          simp [heqi, hne]
      · simp only [hi0, ↓reduceIte, hik]
        have hnk : ¬ (i.val ≤ k) := by omega
        have hne1 : i ≠ ⟨k, by omega⟩ := by simp [Fin.ext_iff]; omega
        have hne2 : i ≠ ⟨k + 1, by omega⟩ := by simp [Fin.ext_iff]; omega
        simp [hnk, hne1, hne2]

/-! ### Section 3: Exact split and merge reversible circuits on `inCodeA` / `outCodeA` -/

lemma two_le_labW (D : FieldData) : 2 ≤ D.labW := by
  by_contra h
  have hle : D.labW ≤ 1 := by omega
  have hpow : D.q ^ 2 ≤ 2 ^ 1 := (Nat.clog_le_iff_le_pow (by decide)).mp hle
  have := D.one_lt_q
  nlinarith

lemma inCodeA_bit0_0 (D : FieldData) (x : InReg D) :
    inCodeA D x ⟨0, by have := two_le_labW D; omega⟩ =
      match x.1.1 with | .inl _ => false | .inr _ => true := by
  have h2 := two_le_labW D
  simp only [inCodeA, packNat]
  have h0d : (0 : ℕ) / D.labW = 0 := Nat.zero_div _
  have h0m : (0 : ℕ) % D.labW = 0 := Nat.zero_mod _
  simp only [h0d, h0m]
  cases x.1.1 <;> simp [birrFields]

lemma inCodeA_bit0_7 (D : FieldData) (x : InReg D) :
    inCodeA D x ⟨7 * D.labW, by have := two_le_labW D; omega⟩ =
      match x.1.2.2.2 with | .inl _ => false | .inr _ => true := by
  have h2 := two_le_labW D
  simp only [inCodeA, packNat]
  have hd : (7 * D.labW) / D.labW = 7 := Nat.mul_div_left 7 (by omega)
  have hm : (7 * D.labW) % D.labW = 0 := Nat.mul_mod_left 7 D.labW
  simp only [hd, hm]
  cases x.1.2.2.2 <;> simp [birrFields]

lemma isHardIn_eq_inCodeA_and (D : FieldData) (x : InReg D) :
    isHardIn D x =
      (inCodeA D x ⟨0, by have := two_le_labW D; omega⟩ &&
        inCodeA D x ⟨7 * D.labW, by have := two_le_labW D; omega⟩) := by
  rw [inCodeA_bit0_0, inCodeA_bit0_7]
  unfold isHardIn
  cases x.1.1 <;> cases x.1.2.2.2 <;> rfl

lemma outCodeA_bit0_0 (D : FieldData) (y : OutReg D) :
    outCodeA D y ⟨0, by have := two_le_labW D; omega⟩ =
      match y.1 with | .inl _ => false | .inr _ => true := by
  have h2 := two_le_labW D
  simp only [outCodeA, packNat]
  have h0d : (0 : ℕ) / D.labW = 0 := Nat.zero_div _
  have h0m : (0 : ℕ) % D.labW = 0 := Nat.zero_mod _
  simp only [h0d, h0m]
  cases y.1 <;> simp [birrFields]

lemma outCodeA_bit0_6 (D : FieldData) (y : OutReg D) :
    outCodeA D y ⟨6 * D.labW, by have := two_le_labW D; omega⟩ =
      match y.2.2 with | .inl _ => false | .inr _ => true := by
  have h2 := two_le_labW D
  simp only [outCodeA, packNat]
  have hd : (6 * D.labW) / D.labW = 6 := Nat.mul_div_left 6 (by omega)
  have hm : (6 * D.labW) % D.labW = 0 := Nat.mul_mod_left 6 D.labW
  simp only [hd, hm]
  cases y.2.2 <;> simp [birrFields]

lemma isHardOut_eq_outCodeA_and (D : FieldData) (y : OutReg D) :
    isHardOut D y =
      (outCodeA D y ⟨0, by have := two_le_labW D; omega⟩ &&
        outCodeA D y ⟨6 * D.labW, by have := two_le_labW D; omega⟩) := by
  rw [outCodeA_bit0_0, outCodeA_bit0_6]
  unfold isHardOut
  cases y.1 <;> cases y.2.2 <;> rfl

def splitInGate (D : FieldData) : RevGate (1 + 10 * D.labW) :=
  RevGate.ccx ⟨1, by have := two_le_labW D; omega⟩
    ⟨1 + 7 * D.labW, by have := two_le_labW D; omega⟩
    ⟨0, by omega⟩
    (by have := two_le_labW D; simp [Fin.ext_iff]; omega)
    (by simp [Fin.ext_iff])
    (by have := two_le_labW D; simp [Fin.ext_iff])

def splitInRev (D : FieldData) : List (RevGate (1 + 10 * D.labW)) :=
  shiftUpAux (by omega : 10 * D.labW < 1 + 10 * D.labW) (10 * D.labW) le_rfl ++ [splitInGate D]

def splitInCirc (D : FieldData) : List (Instr (1 + 10 * D.labW)) :=
  compileRev (splitInRev D)

def mergeOutGate (D : FieldData) : RevGate (1 + 9 * D.labW) :=
  RevGate.ccx ⟨1, by have := two_le_labW D; omega⟩
    ⟨1 + 6 * D.labW, by have := two_le_labW D; omega⟩
    ⟨0, by omega⟩
    (by have := two_le_labW D; simp [Fin.ext_iff]; omega)
    (by simp [Fin.ext_iff])
    (by have := two_le_labW D; simp [Fin.ext_iff])

def mergeOutRev (D : FieldData) : List (RevGate (1 + 9 * D.labW)) :=
  [mergeOutGate D] ++
    (shiftUpAux (by omega : 9 * D.labW < 1 + 9 * D.labW) (9 * D.labW) le_rfl).reverse

def mergeOutCirc (D : FieldData) : List (Instr (1 + 9 * D.labW)) :=
  compileRev (mergeOutRev D)

lemma sumCode_eq_pad_tag {X₀ X₁ : Type} {W : ℕ} (c₀ : X₀ → Qubits W) (c₁ : X₁ → Qubits W)
    (s : X₀ ⊕ X₁) (i : Fin (1 + W)) :
    padTo (1 + W) (sumCode c₀ c₁ s) i =
      if h0 : i.val = 0 then
        match s with | .inl _ => false | .inr _ => true
      else
        match s with
        | .inl x => c₀ x ⟨i.val - 1, by have := i.isLt; omega⟩
        | .inr x => c₁ x ⟨i.val - 1, by have := i.isLt; omega⟩ := by
  have hi_max : i.val < 1 + max W W := by rw [Nat.max_self]; exact i.isLt
  simp only [padTo, dif_pos hi_max]
  by_cases h0 : i.val = 0
  · simp only [dif_pos h0]
    have hlt1 : (⟨i.val, hi_max⟩ : Fin (1 + max W W)).val < 1 := by simp [h0]
    cases s with
    | inl x =>
      change Fin.append (fun _ : Fin 1 => false) (padTo (max W W) (c₀ x)) ⟨i.val, hi_max⟩ = false
      simp [Fin.append, Fin.addCases, hlt1]
    | inr x =>
      change Fin.append (fun _ : Fin 1 => true) (padTo (max W W) (c₁ x)) ⟨i.val, hi_max⟩ = true
      simp [Fin.append, Fin.addCases, hlt1]
  · simp only [dif_neg h0]
    have hnot1 : ¬ ((⟨i.val, hi_max⟩ : Fin (1 + max W W)).val < 1) := by dsimp; omega
    have hi_sub : i.val - 1 < W := by have := i.isLt; omega
    cases s with
    | inl x =>
      change Fin.append (fun _ : Fin 1 => false) (padTo (max W W) (c₀ x)) ⟨i.val, hi_max⟩ = _
      simp [Fin.append, Fin.addCases, hnot1, padTo, hi_sub]
    | inr x =>
      change Fin.append (fun _ : Fin 1 => true) (padTo (max W W) (c₁ x)) ⟨i.val, hi_max⟩ = _
      simp [Fin.append, Fin.addCases, hnot1, padTo, hi_sub]

lemma act_splitInCirc (D : FieldData) (x : InReg D) :
    act (circUnitary (splitInCirc D)) (ket (padTo (1 + 10 * D.labW) (inCodeA D x))) =
      ket (padTo (1 + 10 * D.labW)
        (sumCode (fun z : InRegNonHard D => inCodeA D z.1) (fun z : InRegHard D => inCodeA D z.1)
          (splitInA D x))) := by
  have h2 := two_le_labW D
  rw [splitInCirc, circUnitary_compileRev, act_permMat]
  congr 1
  rw [splitInRev, evalRev_append, evalRev_shiftUpAux]
  set q1 : Qubits (1 + 10 * D.labW) :=
    fun i => if i.val = 0 then padTo (1 + 10 * D.labW) (inCodeA D x) ⟨10 * D.labW, by omega⟩
      else if i.val ≤ 10 * D.labW then padTo (1 + 10 * D.labW) (inCodeA D x) ⟨i.val - 1, by omega⟩
      else padTo (1 + 10 * D.labW) (inCodeA D x) i
  have hq1_0 : q1 ⟨0, by omega⟩ = false := by
    simp [q1, padTo]
  have hq1_succ : ∀ j : Fin (10 * D.labW), q1 ⟨j.val + 1, by omega⟩ = inCodeA D x j := by
    intro j
    have hjle : j.val + 1 ≤ 10 * D.labW := by omega
    simp only [q1, show j.val + 1 ≠ 0 by omega, ↓reduceIte, hjle, Nat.add_sub_cancel, padTo,
      dif_pos j.isLt]
  have hccx : evalRev [splitInGate D] q1 =
      Function.update q1 ⟨0, by omega⟩ (xor (q1 ⟨0, by omega⟩)
        (q1 ⟨1, by omega⟩ && q1 ⟨1 + 7 * D.labW, by omega⟩)) := by
    simp [evalRev, splitInGate, RevGate.eval]
  rw [hccx]
  ext i
  rw [sumCode_eq_pad_tag]
  by_cases hi0 : i.val = 0
  · have hi_fin : i = ⟨0, by omega⟩ := Fin.ext hi0
    rw [hi_fin]
    simp only [Function.update_self, hq1_0, Bool.false_xor, Fin.val_zero, dite_true]
    have h1 := hq1_succ ⟨0, by omega⟩
    have h7 := hq1_succ ⟨7 * D.labW, by omega⟩
    have h1eq : (⟨1, by omega⟩ : Fin (1 + 10 * D.labW)) = ⟨0 + 1, by omega⟩ := rfl
    have h7eq : (⟨1 + 7 * D.labW, by omega⟩ : Fin (1 + 10 * D.labW)) = ⟨7 * D.labW + 1, by omega⟩ := by
      ext; simp; omega
    rw [h1eq, h1, h7eq, h7, ← isHardIn_eq_inCodeA_and]
    unfold splitInA
    split_ifs with hh
    · simp [hh]
    · simp [Bool.eq_false_iff.mpr hh]
  · have hi_ne : i ≠ ⟨0, by omega⟩ := fun h => hi0 (congrArg Fin.val h)
    rw [Function.update_of_ne hi_ne]
    simp only [dif_neg hi0]
    have hile : i.val ≤ 10 * D.labW := by omega
    have hq1_i : q1 i = inCodeA D x ⟨i.val - 1, by omega⟩ := by
      have hi_eq : q1 i = q1 ⟨(i.val - 1) + 1, by omega⟩ := by congr 1; ext; simp; omega
      rw [hi_eq]
      exact hq1_succ ⟨i.val - 1, by omega⟩
    rw [hq1_i]
    unfold splitInA
    split_ifs <;> rfl

lemma act_mergeOutCirc (D : FieldData) (s : OutRegNonHard D ⊕ OutRegHard D) :
    act (circUnitary (mergeOutCirc D))
        (ket (padTo (1 + 9 * D.labW)
          (sumCode (fun y : OutRegNonHard D => outCodeA D y.1) (fun y : OutRegHard D => outCodeA D y.1) s))) =
      ket (padTo (1 + 9 * D.labW) (outCodeA D (mergeOutA D s))) := by
  have h2 := two_le_labW D
  rw [mergeOutCirc, circUnitary_compileRev, act_permMat]
  congr 1
  rw [mergeOutRev, evalRev_append]
  set y : OutReg D := mergeOutA D s
  set q0 : Qubits (1 + 9 * D.labW) :=
    padTo (1 + 9 * D.labW)
      (sumCode (fun z : OutRegNonHard D => outCodeA D z.1) (fun z : OutRegHard D => outCodeA D z.1) s)
  have hshift_target :
      evalRev [mergeOutGate D] q0 =
        evalRev (shiftUpAux (by omega : 9 * D.labW < 1 + 9 * D.labW) (9 * D.labW) le_rfl)
          (padTo (1 + 9 * D.labW) (outCodeA D y)) := by
    rw [evalRev_shiftUpAux]
    rw [evalRev_cons, evalRev_nil]
    dsimp only [mergeOutGate, RevGate.eval]
    ext i
    by_cases hi0 : i.val = 0
    · have hi_fin : i = ⟨0, by omega⟩ := Fin.ext hi0
      rw [hi_fin]
      simp only [Function.update_self, Fin.val_zero, ↓reduceIte]
      have h0_tag : q0 ⟨0, by omega⟩ = isHardOut D y := by
        simp only [q0, sumCode_eq_pad_tag, Fin.val_zero, dite_true]
        cases s with
        | inl y0 => simpa [y, mergeOutA] using y0.2.symm
        | inr y1 => simpa [y, mergeOutA] using y1.2.symm
      have h1_tag : q0 ⟨1, by omega⟩ = outCodeA D y ⟨0, by omega⟩ := by
        simp only [q0, sumCode_eq_pad_tag]
        cases s <;> rfl
      have h6_tag : q0 ⟨1 + 6 * D.labW, by omega⟩ = outCodeA D y ⟨6 * D.labW, by omega⟩ := by
        simp only [q0, sumCode_eq_pad_tag]
        have hnz : (1 + 6 * D.labW : ℕ) ≠ 0 := by omega
        simp only [dif_neg hnz, Nat.add_sub_cancel_left]
        cases s <;> rfl
      have hpad_end : padTo (1 + 9 * D.labW) (outCodeA D y) ⟨9 * D.labW, by omega⟩ = false := by
        simp [padTo]
      rw [h0_tag, h1_tag, h6_tag, ← isHardOut_eq_outCodeA_and, Bool.xor_self, hpad_end]
    · have hi_ne : i ≠ ⟨0, by omega⟩ := fun h => hi0 (congrArg Fin.val h)
      rw [Function.update_of_ne hi_ne]
      have hile : i.val ≤ 9 * D.labW := by omega
      simp only [hi0, ↓reduceIte, hile, padTo, show i.val - 1 < 9 * D.labW by omega, dite_true]
      simp only [q0, sumCode_eq_pad_tag, dif_neg hi0]
      cases s <;> rfl
  rw [hshift_target, evalRev_reverse]

/-! ### Section 4: Polynomial-time TM2 compiler for `splitInCirc` and `mergeOutCirc` -/

lemma natBits_length_le_iff {n k : ℕ} : n.bits.length ≤ k ↔ n < 2 ^ k := by
  induction n using Nat.binaryRec generalizing k with
  | zero => simp
  | bit b n ih =>
    by_cases h0 : n = 0 ∧ b = false
    · rcases h0 with ⟨rfl, rfl⟩; simp [Nat.bit]
    · have hne : n = 0 → b = true := fun hn => by cases hb : b <;> simp_all
      rw [Nat.bits_append_bit n b hne, List.length_cons]
      cases k with
      | zero =>
        simp only [Nat.le_zero_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_iff,
          not_lt, pow_zero]
        cases b
        · simp only [Nat.bit, cond_false]
          exact Nat.pos_of_ne_zero fun hn => h0 ⟨by omega, rfl⟩
        · simp [Nat.bit]
      | succ k =>
        rw [Nat.add_le_add_iff_right, ih, Nat.pow_succ']
        cases b <;> simp [Nat.bit] <;> omega

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

@[fun_prop]
lemma poly_decodeBits : Automatic.Poly decodeBits := by
  have hstep : Automatic.Poly (fun p : ℕ × Bool => 2 * p.1 + if p.2 then 1 else 0) := by fun_prop
  have hfold : Automatic.Poly
      (fun x : List Bool × ℕ => List.foldl (fun acc b => 2 * acc + if b then 1 else 0) x.2 x.1) := by
    rcases hstep with ⟨Ps⟩
    refine ⟨PolyProgram.listFoldLinear Ps false 1 fun b a => ?_⟩
    have hstep_le : (2 * b + if a then 1 else 0).bits.length ≤ b.bits.length + 1 := by
      rw [natBits_length_le_iff, Nat.pow_succ']
      have hb0 := natBits_length_le_iff.mp (le_refl b.bits.length)
      cases a <;> simp <;> omega
    exact hstep_le.trans (by
      change _ ≤ b.bits.length + 1 * (2 * (encodeBool a).length + 1)
      omega)
  have hrev : Automatic.Poly (fun bs : List Bool => bs.reverse) := by fun_prop
  have h0 : Automatic.Poly (fun _ : List Bool => (0 : ℕ)) := by fun_prop
  rcases hrev with ⟨Prev⟩
  rcases h0 with ⟨P0⟩
  rcases hfold with ⟨Pfold⟩
  exact ⟨((Prev.fanout P0).comp Pfold).congr _ (fun _ => rfl)⟩

@[fun_prop]
lemma poly_decodeBits_comp {α : Type} [Automatic.Coding α] {bs : α → List Bool} (hbs : Automatic.Poly bs) :
    Automatic.Poly (fun x => decodeBits (bs x)) := by
  rcases hbs with ⟨Pbs⟩; rcases poly_decodeBits with ⟨Pd⟩
  exact ⟨(Pbs.comp Pd).congr _ (fun _ => rfl)⟩

lemma decodeBits_bits (n : ℕ) : decodeBits n.bits = n := by
  induction n using Nat.binaryRec with
  | zero => rfl
  | bit b n ih =>
    by_cases h0 : n = 0 ∧ b = false
    · rcases h0 with ⟨rfl, rfl⟩; simp [Nat.bit, decodeBits]
    · have hne : n = 0 → b = true := fun hn => by
        cases hb : b
        · exact absurd ⟨hn, hb⟩ h0
        · rfl
      simp only [decodeBits, Nat.bits_append_bit n b hne, List.reverse_cons, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      change 2 * decodeBits n.bits + (if b then 1 else 0) = Nat.bit b n
      rw [ih]
      cases b <;> simp [Nat.bit]

def prodList (as : List ℕ) : ℕ := as.foldl (· * ·) 1

lemma natBits_mul_length_le (x y : ℕ) :
    (x * y).bits.length ≤ x.bits.length + y.bits.length := by
  rw [natBits_length_le_iff, Nat.pow_add]
  have hx := natBits_length_le_iff.mp (le_refl x.bits.length)
  have hy := natBits_length_le_iff.mp (le_refl y.bits.length)
  exact Nat.mul_lt_mul_of_lt_of_lt hx hy

@[fun_prop]
lemma poly_prodList : Automatic.Poly prodList := by
  have hop : Automatic.Poly (fun p : ℕ × ℕ => p.1 * p.2) := by fun_prop
  have hfold : Automatic.Poly (fun x : List ℕ × ℕ => List.foldl (· * ·) x.2 x.1) := by
    rcases hop with ⟨Pop⟩
    refine ⟨PolyProgram.listFoldLinear Pop 0 1 fun b a => ?_⟩
    have hmul := natBits_mul_length_le b a
    exact hmul.trans (by change _ ≤ b.bits.length + 1 * (2 * a.bits.length + 1); omega)
  have hid : Automatic.Poly (fun as : List ℕ => as) := by fun_prop
  have h1 : Automatic.Poly (fun _ : List ℕ => (1 : ℕ)) := by fun_prop
  rcases hid with ⟨Pid⟩
  rcases h1 with ⟨P1⟩
  rcases hfold with ⟨Pfold⟩
  exact ⟨((Pid.fanout P1).comp Pfold).congr _ (fun _ => rfl)⟩

@[fun_prop]
lemma poly_prodList_comp {α : Type} [Automatic.Coding α] {as : α → List ℕ} (has : Automatic.Poly as) :
    Automatic.Poly (fun x => prodList (as x)) := by
  rcases has with ⟨Pas⟩; rcases poly_prodList with ⟨Pp⟩
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

lemma flatMap_pair_length (bs : List Bool) :
    (bs.flatMap (fun β => [true, β])).length = 2 * bs.length := by
  induction bs with | nil => simp | cons _ _ ih => simp; omega

lemma flatMap_pair_getElem_even (bs : List Bool) (j : ℕ) (hj : j < bs.length) :
    (bs.flatMap (fun β => [true, β]))[2 * j]'(by rw [flatMap_pair_length]; omega) = true := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons hd tl ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.flatMap_cons, List.cons_append]
      simpa [show 2 * (j + 1) = (2 * j + 1) + 1 by omega] using ih j (by simpa using hj)

lemma flatMap_pair_getElem_odd (bs : List Bool) (j : ℕ) (hj : j < bs.length) :
    (bs.flatMap (fun β => [true, β]))[2 * j + 1]'(by rw [flatMap_pair_length]; omega) = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons hd tl ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.flatMap_cons, List.cons_append]
      simpa [show 2 * (j + 1) + 1 = (2 * j + 1 + 1) + 1 by omega] using ih j (by simpa using hj)

lemma encBin_getElem_even {m j : ℕ} (hj : j < m.bits.length) :
    (encBin m)[2 * j]'(by rw [encBin_length]; omega) = true := by
  simp only [encBin]
  rw [List.getElem_append_left (by rw [flatMap_pair_length]; omega)]
  exact flatMap_pair_getElem_even m.bits j hj

lemma encBin_getElem_odd {m j : ℕ} (hj : j < m.bits.length) :
    (encBin m)[2 * j + 1]'(by rw [encBin_length]; omega) = m.bits[j] := by
  simp only [encBin]
  rw [List.getElem_append_left (by rw [flatMap_pair_length]; omega)]
  exact flatMap_pair_getElem_odd m.bits j hj

lemma encBin_getElem?_end (m : ℕ) :
    (encBin m)[2 * m.bits.length]? = some false := by
  simp only [encBin]
  rw [List.getElem?_append_right (by rw [flatMap_pair_length]), flatMap_pair_length, Nat.sub_self]
  rfl

lemma encBin_getElem?_even {m j : ℕ} (hj : j < m.bits.length) :
    (encBin m)[2 * j]? = some true := by
  rw [List.getElem?_eq_getElem (by rw [encBin_length]; omega), encBin_getElem_even hj]

lemma encBin_getElem?_odd {m j : ℕ} (hj : j < m.bits.length) :
    (encBin m)[2 * j + 1]? = some m.bits[j] := by
  rw [List.getElem?_eq_getElem (by rw [encBin_length]; omega), encBin_getElem_odd hj]

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
  rcases hxs with ⟨Pxs⟩; rcases hs with ⟨Ps⟩; rcases poly_binEndAfter_pair with ⟨Pb⟩
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
  rcases hxs with ⟨Pxs⟩; rcases hs with ⟨Ps⟩; rcases poly_parseBinFrom_pair with ⟨Pp⟩
  exact ⟨((Pxs.fanout Ps).comp Pp).congr _ (fun _ => rfl)⟩

lemma head?_filter_range {N E : ℕ} (p : ℕ → Bool) (hEN : E < N)
    (hpre : ∀ i < E, p i = false) (hpE : p E = true) :
    ((List.range N).filter p).head?.getD 0 = E := by
  obtain ⟨d, hN⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hEN)
  have hr : List.range N = List.range E ++ E :: (List.range d).map (fun t => E + 1 + t) := by
    rw [hN, List.range_add, List.range_succ]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hr, List.filter_append]
  have hnil : (List.range E).filter p = [] :=
    List.filter_eq_nil_iff.mpr fun i hi => by
      rw [List.mem_range] at hi; simp [hpre i hi]
  rw [hnil, List.nil_append, List.filter_cons, hpE]
  rfl

lemma binEndAfter_eq (pre : List Bool) (m : ℕ) (suf : List Bool)
    (heven : ∃ s, pre.length = 2 * s) :
    binEndAfter (pre ++ encBin m ++ suf) pre.length = pre.length + 2 * m.bits.length := by
  rcases heven with ⟨s, hs⟩
  unfold binEndAfter
  have hlen : pre.length + 2 * m.bits.length < (pre ++ encBin m ++ suf).length := by
    simp only [List.length_append, encBin_length]; omega
  refine head?_filter_range _ hlen ?_ ?_
  · intro i hi
    by_cases hsi : i < pre.length
    · simp [show ¬ (pre.length ≤ i) by omega]
    · have him : i - pre.length < 2 * m.bits.length := by omega
      have hsub_len : i - pre.length < (encBin m).length := by rw [encBin_length]; omega
      by_cases hb : Nat.bodd i
      · simp [hb]
      · have hbi : Nat.bodd (i - pre.length) = false := by
          have hbe : Nat.bodd (2 * s) = false := by simp [Nat.bodd_mul]
          have hieq : i = 2 * s + (i - 2 * s) := by omega
          rw [hs] at *
          have hadd := congrArg Nat.bodd hieq
          rw [Nat.bodd_add, hbe] at hadd
          simp only [Bool.false_xor] at hadd
          rw [← hadd]
          simpa using hb
        have heq_two : i - pre.length = 2 * ((i - pre.length) / 2) := by
          have hmod : (i - pre.length) % 2 = 0 := by
            rw [Nat.mod_two_of_bodd, hbi]; rfl
          omega
        have hj : (i - pre.length) / 2 < m.bits.length := by omega
        have hget : (pre ++ encBin m ++ suf)[i]? = some true := by
          rw [List.append_assoc, List.getElem?_append_right (by omega),
            List.getElem?_append_left hsub_len, heq_two]
          exact encBin_getElem?_even hj
        rw [hget]
        simp
  · have hsub_len : 2 * m.bits.length < (encBin m).length := by rw [encBin_length]; omega
    have hb : Nat.bodd (pre.length + 2 * m.bits.length) = false := by
      rw [hs, ← Nat.mul_add, Nat.bodd_mul]; simp
    have hget : (pre ++ encBin m ++ suf)[pre.length + 2 * m.bits.length]? = some false := by
      rw [List.append_assoc, List.getElem?_append_right (by omega),
        Nat.add_sub_cancel_left, List.getElem?_append_left hsub_len]
      exact encBin_getElem?_end m
    rw [hget]
    simp [hb]

lemma filter_range_odd_between (N s k : ℕ) (hN : 2 * s + 2 * k ≤ N) :
    (List.range N).filter (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * k) && Nat.bodd i) =
      (List.range k).map (fun j => 2 * s + 2 * j + 1) := by
  induction k with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, List.range_zero, List.map_nil]
    apply List.filter_eq_nil_iff.mpr
    intro i _
    simp
  | succ k ih =>
    have hk : 2 * s + 2 * k + 1 < N := by omega
    have hr : (List.range N).filter (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * (k + 1)) && Nat.bodd i) =
        (List.range N).filter (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * k) && Nat.bodd i) ++
          [2 * s + 2 * k + 1] := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hk)
      have hsplit : List.range N = List.range (2 * s + 2 * k) ++
          [2 * s + 2 * k, 2 * s + 2 * k + 1] ++ (List.range d).map (fun t => 2 * s + 2 * k + 2 + t) := by
        rw [hd, List.range_add, List.range_succ, List.range_succ]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [hsplit]
      have hnil_left1 : (List.range (2 * s + 2 * k)).filter
          (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * (k + 1)) && Nat.bodd i) =
          (List.range (2 * s + 2 * k)).filter
          (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * k) && Nat.bodd i) := by
        apply List.filter_congr
        intro i hi; rw [List.mem_range] at hi; simp [hi, show i < 2 * s + 2 * (k + 1) by omega]
      have hnil_right0 : ((List.range d).map (fun t => 2 * s + 2 * k + 2 + t)).filter
          (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * k) && Nat.bodd i) = [] :=
        List.filter_eq_nil_iff.mpr fun i hi => by
          obtain ⟨t, _, rfl⟩ := List.mem_map.mp hi; simp; omega
      have hnil_right1 : ((List.range d).map (fun t => 2 * s + 2 * k + 2 + t)).filter
          (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * (k + 1)) && Nat.bodd i) = [] :=
        List.filter_eq_nil_iff.mpr fun i hi => by
          obtain ⟨t, _, rfl⟩ := List.mem_map.mp hi; simp; omega
      have hmid0 : [2 * s + 2 * k, 2 * s + 2 * k + 1].filter
          (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * k) && Nat.bodd i) = [] := by
        simp [show ¬ (2 * s + 2 * k + 1 < 2 * s + 2 * k) by omega]
      have hb_even : Nat.bodd (2 * s + 2 * k) = false := by
        rw [← Nat.mul_add, Nat.bodd_mul]; simp
      have hb_odd : Nat.bodd (2 * s + 2 * k + 1) = true := by
        rw [Nat.bodd_add, hb_even]; decide
      have hmid1 : [2 * s + 2 * k, 2 * s + 2 * k + 1].filter
          (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * (k + 1)) && Nat.bodd i) =
          [2 * s + 2 * k + 1] := by
        simp [hb_even, hb_odd, show 2 * s ≤ 2 * s + 2 * k + 1 by omega,
          show 2 * s + 2 * k + 1 < 2 * s + 2 * (k + 1) by omega]
      simp only [List.filter_append, hnil_left1, hmid0, hmid1, hnil_right0, hnil_right1, List.append_nil]
    rw [hr, ih (by omega), List.range_succ, List.map_append]
    rfl

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
    apply List.ext_getElem
    · simp
    · intro j hj1 hj2
      simp only [List.length_map, List.length_range] at hj1
      simp only [List.getElem_map, List.getElem_range]
      have hlt_sub : 2 * j + 1 < (encBin m).length := by rw [encBin_length]; omega
      have hget : (pre ++ encBin m ++ suf)[2 * s + 2 * j + 1]? = some m.bits[j] := by
        rw [List.append_assoc, List.getElem?_append_right (by omega),
          show 2 * s + 2 * j + 1 - pre.length = 2 * j + 1 by omega,
          List.getElem?_append_left hlt_sub]
        exact encBin_getElem?_odd hj1
      rw [hget, Option.getD_some]
  rw [hmap, decodeBits_bits]

lemma filter_range_lt_eq {N n : ℕ} (hn : n ≤ N) :
    (List.range N).filter (fun i => decide (i < n)) = List.range n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [List.range_add, List.filter_append]
  have h1 : (List.range n).filter (fun i => decide (i < n)) = List.range n :=
    List.filter_eq_self.mpr fun i hi => by rw [List.mem_range] at hi; simp [hi]
  have h2 : ((List.range d).map (n + ·)).filter (fun i => decide (i < n)) = [] :=
    List.filter_eq_nil_iff.mpr fun i hi => by
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hi; simp
  rw [h1, h2, List.append_nil]

def pRaw (xs : List Bool) : ℕ := parseBinFrom xs 0
def pEndRaw (xs : List Bool) : ℕ := binEndAfter xs 0
def rRaw (xs : List Bool) : ℕ := parseBinFrom xs (pEndRaw xs + 2)
def qRaw (xs : List Bool) : ℕ :=
  prodList (((List.range xs.length).filter (fun i => decide (i < rRaw xs))).map (fun _ => pRaw xs))
def labWRaw (xs : List Bool) : ℕ :=
  (qRaw xs * qRaw xs - 1).bits.length

@[fun_prop] lemma poly_pRaw : Automatic.Poly pRaw := by unfold pRaw; fun_prop
@[fun_prop] lemma poly_pEndRaw : Automatic.Poly pEndRaw := by unfold pEndRaw; fun_prop
@[fun_prop] lemma poly_rRaw : Automatic.Poly rRaw := by unfold rRaw; fun_prop
@[fun_prop] lemma poly_qRaw : Automatic.Poly qRaw := by unfold qRaw; fun_prop
@[fun_prop] lemma poly_labWRaw : Automatic.Poly labWRaw := by unfold labWRaw; fun_prop

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
  have h2 := flatMap_encBin_length_ge (List.range (D.r + 1)) (fun j => (D.f.coeff j).val)
  simp only [List.length_append, List.length_range] at *
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

def rawSwap (a b : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(4, a, b), (4, b, a), (4, a, b)]

@[fun_prop]
lemma poly_rawSwap_pair : Automatic.Poly (fun p : ℕ × ℕ => rawSwap p.1 p.2) := by
  unfold rawSwap; fun_prop

def fuelVec (xs : List Bool) : List ℕ :=
  (true :: true :: xs).flatMap (fun _ =>
    (true :: true :: xs).flatMap (fun _ =>
      (true :: true :: xs).flatMap (fun _ => List.range 2048)))

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

@[fun_prop] lemma poly_fuelVec : Automatic.Poly fuelVec := by unfold fuelVec; fun_prop
@[fun_prop] lemma poly_fuelIdx : Automatic.Poly fuelIdx := by unfold fuelIdx; fun_prop
@[fun_prop] lemma poly_rangeFuel : Automatic.Poly (fun p : List ℕ × ℕ => rangeFuel p.1 p.2) := by
  unfold rangeFuel; fun_prop
@[fun_prop] lemma poly_encNatFuel : Automatic.Poly (fun p : List ℕ × ℕ => encNatFuel p.1 p.2) := by
  unfold encNatFuel; fun_prop
@[fun_prop] lemma poly_encRawInstrFuel :
    Automatic.Poly (fun p : List ℕ × (ℕ × ℕ × ℕ) => encRawInstrFuel p.1 p.2) := by
  unfold encRawInstrFuel; fun_prop
@[fun_prop] lemma poly_encRawLayerFuel :
    Automatic.Poly (fun p : List ℕ × List (ℕ × ℕ × ℕ) => encRawLayerFuel p.1 p.2) := by
  unfold encRawLayerFuel; fun_prop

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
  | h i => simp [toRawInstr, encRawInstrFuel, encInstr, encNatFuel_eq (by omega : 0 ≤ F), encNatFuel_eq (by omega : i.val ≤ F)]
  | s i => simp [toRawInstr, encRawInstrFuel, encInstr, encNatFuel_eq (by omega : 1 ≤ F), encNatFuel_eq (by omega : i.val ≤ F)]
  | t i => simp [toRawInstr, encRawInstrFuel, encInstr, encNatFuel_eq (by omega : 2 ≤ F), encNatFuel_eq (by omega : i.val ≤ F)]
  | x i => simp [toRawInstr, encRawInstrFuel, encInstr, encNatFuel_eq (by omega : 3 ≤ F), encNatFuel_eq (by omega : i.val ≤ F)]
  | cnot i j _ =>
    simp [toRawInstr, encRawInstrFuel, encInstr, encNatFuel_eq (by omega : 4 ≤ F),
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

lemma shiftUpAux_toRaw {W N : ℕ} (hWN : W < N) (k : ℕ) (hk : k ≤ W) :
    (compileRev (shiftUpAux hWN k hk)).map toRawInstr =
      ((List.range k).reverse).flatMap (fun j => rawSwap j (j + 1)) := by
  induction k with
  | zero => simp [shiftUpAux, compileRev]
  | succ k ih =>
    simp only [shiftUpAux, compileRev_append, List.map_append, List.range_succ, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.flatMap_cons,
      ih (by omega)]
    congr 1

lemma shiftUpAux_rev_toRaw {W N : ℕ} (hWN : W < N) (k : ℕ) (hk : k ≤ W) :
    (compileRev (shiftUpAux hWN k hk).reverse).map toRawInstr =
      (List.range k).flatMap (fun j => rawSwap j (j + 1)) := by
  induction k with
  | zero => simp [shiftUpAux, compileRev]
  | succ k ih =>
    simp only [shiftUpAux, List.reverse_append, compileRev_append, List.map_append,
      List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      ih (by omega)]
    congr 1

lemma fuelVec_length_eq (xs : List Bool) :
    (fuelVec xs).length = (xs.length + 2) ^ 3 * 2048 := by
  have h1 : ∀ {α β} (l : List α) (f : α → List β) (k : ℕ),
      (∀ a, (f a).length = k) → (l.flatMap f).length = l.length * k := by
    intro α β l f k hk
    induction l with
    | nil => simp
    | cons a tl ih => simp [hk a, ih]; ring
  unfold fuelVec
  rw [h1 _ _ ((xs.length + 2) ^ 2 * 2048)]
  · simp; ring
  · intro _
    rw [h1 _ _ ((xs.length + 2) * 2048)]
    · simp; ring
    · intro _
      rw [h1 _ _ 2048 (fun _ => by simp)]
      simp

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
  have hp_len : D.p.bits.length ≤ D.encData.length := by
    obtain ⟨suf, hsuf⟩ := encData_eq_encBin_p_r D
    rw [hsuf, List.length_append, List.length_append, encBin_length]
    omega
  have hr_len : D.r ≤ D.encData.length := encData_length_ge_r D
  calc D.labW ≤ 2 * D.p.bits.length * D.r := hclog
    _ ≤ 2 * D.encData.length * D.encData.length := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hp_len) hr_len
    _ = 2 * D.encData.length ^ 2 := by ring

lemma labW_le_two_log2_q_add_two (D : FieldData) : D.labW ≤ 2 * Nat.log 2 D.q + 2 := by
  unfold FieldData.labW
  rw [Nat.clog_le_iff_le_pow (by decide)]
  have hq : D.q < 2 ^ (Nat.log 2 D.q + 1) := Nat.lt_pow_succ_log_self (by decide) D.q
  have hq2 : D.q ^ 2 < 2 ^ (2 * Nat.log 2 D.q + 2) := by
    calc D.q ^ 2 = D.q * D.q := sq D.q
      _ < 2 ^ (Nat.log 2 D.q + 1) * 2 ^ (Nat.log 2 D.q + 1) := Nat.mul_lt_mul_of_lt_of_lt hq hq
      _ = 2 ^ (2 * Nat.log 2 D.q + 2) := by rw [← Nat.pow_add]; ring_nf
  exact le_of_lt hq2

def splitInRawLayer (fuel : List ℕ) (L : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((rangeFuel fuel (10 * L)).reverse).flatMap (fun j => rawSwap j (j + 1)) ++
    rawCcx 1 (1 + 7 * L) 0

@[fun_prop]
lemma poly_splitInRawLayer :
    Automatic.Poly (fun p : List ℕ × ℕ => splitInRawLayer p.1 p.2) := by
  unfold splitInRawLayer rangeFuel rawCcx
  fun_prop

def splitInBuilder (xs : List Bool) : Str :=
  encNatFuel (fuelIdx xs) (1 + 10 * labWRaw xs) ++
    encRawLayerFuel (fuelIdx xs) (splitInRawLayer (fuelIdx xs) (labWRaw xs))

def mergeOutRawLayer (fuel : List ℕ) (L : ℕ) : List (ℕ × ℕ × ℕ) :=
  rawCcx 1 (1 + 6 * L) 0 ++
    (rangeFuel fuel (9 * L)).flatMap (fun j => rawSwap j (j + 1))

@[fun_prop]
lemma poly_mergeOutRawLayer :
    Automatic.Poly (fun p : List ℕ × ℕ => mergeOutRawLayer p.1 p.2) := by
  unfold mergeOutRawLayer rangeFuel rawCcx
  fun_prop

def mergeOutBuilder (xs : List Bool) : Str :=
  encNatFuel (fuelIdx xs) (1 + 9 * labWRaw xs) ++
    encRawLayerFuel (fuelIdx xs) (mergeOutRawLayer (fuelIdx xs) (labWRaw xs))

lemma poly_splitInBuilder : Automatic.Poly splitInBuilder := by
  rcases poly_fuelIdx with ⟨Pf⟩
  rcases poly_labWRaw with ⟨Pl⟩
  rcases poly_splitInRawLayer with ⟨Pr⟩
  rcases poly_encNatFuel with ⟨Pen⟩
  rcases poly_encRawLayerFuel with ⟨Pel⟩
  rcases (by fun_prop : Automatic.Poly (fun n : ℕ => 1 + 10 * n)) with ⟨Pw⟩
  rcases (Automatic.Poly.list_append : Automatic.Poly fun p : List Bool × List Bool => p.1 ++ p.2) with ⟨Pap⟩
  have P1 : PolyProgram Automatic.enc Automatic.enc (fun xs => encNatFuel (fuelIdx xs) (1 + 10 * labWRaw xs)) :=
    ((Pf.fanout (Pl.comp Pw)).comp Pen).congr _ (fun _ => by dsimp only [Function.comp_def])
  have P2 : PolyProgram Automatic.enc Automatic.enc
      (fun xs => encRawLayerFuel (fuelIdx xs) (splitInRawLayer (fuelIdx xs) (labWRaw xs))) :=
    ((Pf.fanout ((Pf.fanout Pl).comp Pr)).comp Pel).congr _ (fun _ => by dsimp only [Function.comp_def])
  exact ⟨((P1.fanout P2).comp Pap).congr splitInBuilder
    (fun _ => by unfold splitInBuilder; dsimp only [Function.comp_def])⟩

lemma poly_mergeOutBuilder : Automatic.Poly mergeOutBuilder := by
  rcases poly_fuelIdx with ⟨Pf⟩
  rcases poly_labWRaw with ⟨Pl⟩
  rcases poly_mergeOutRawLayer with ⟨Pr⟩
  rcases poly_encNatFuel with ⟨Pen⟩
  rcases poly_encRawLayerFuel with ⟨Pel⟩
  rcases (by fun_prop : Automatic.Poly (fun n : ℕ => 1 + 9 * n)) with ⟨Pw⟩
  rcases (Automatic.Poly.list_append : Automatic.Poly fun p : List Bool × List Bool => p.1 ++ p.2) with ⟨Pap⟩
  have P1 : PolyProgram Automatic.enc Automatic.enc (fun xs => encNatFuel (fuelIdx xs) (1 + 9 * labWRaw xs)) :=
    ((Pf.fanout (Pl.comp Pw)).comp Pen).congr _ (fun _ => by dsimp only [Function.comp_def])
  have P2 : PolyProgram Automatic.enc Automatic.enc
      (fun xs => encRawLayerFuel (fuelIdx xs) (mergeOutRawLayer (fuelIdx xs) (labWRaw xs))) :=
    ((Pf.fanout ((Pf.fanout Pl).comp Pr)).comp Pel).congr _ (fun _ => by dsimp only [Function.comp_def])
  exact ⟨((P1.fanout P2).comp Pap).congr mergeOutBuilder
    (fun _ => by unfold mergeOutBuilder; dsimp only [Function.comp_def])⟩

lemma fuel_bounds_of_labW_le (L len : ℕ) (hL : L ≤ 2 * len ^ 2) :
    10 * L ≤ (len + 2) ^ 3 * 2048 ∧
    1 + 10 * L ≤ (len + 2) ^ 3 * 2048 ∧
    9 * L ≤ (len + 2) ^ 3 * 2048 ∧
    1 + 9 * L ≤ (len + 2) ^ 3 * 2048 ∧
    4 ≤ (len + 2) ^ 3 * 2048 ∧
    25 * (3 * (10 * L) + 1) ≤ (len + 2) ^ 3 * 2048 ∧
    25 * (1 + 3 * (9 * L)) ≤ (len + 2) ^ 3 * 2048 := by
  have hF_ge : 2048 * len ^ 2 + 2048 ≤ (len + 2) ^ 3 * 2048 := by
    have hcube : (len + 2) ^ 3 = (len + 2) * (len + 2) * (len + 2) := by ring
    rw [hcube]
    nlinarith
  omega

lemma splitInBuilder_spec (D : FieldData) (k : ℕ) :
    splitInBuilder (D.encData ++ encNat k) =
      encNat (1 + 10 * D.labW) ++ encLayer (splitInCirc D) := by
  have hlab : labWRaw (D.encData ++ encNat k) = D.labW := labWRaw_encData D k
  have hlab_le : D.labW ≤ 2 * (D.encData ++ encNat k).length ^ 2 :=
    (labW_le_two_encData_sq D).trans (by
      have hlen : D.encData.length ≤ (D.encData ++ encNat k).length := by simp
      nlinarith)
  have hbounds := fuel_bounds_of_labW_le D.labW (D.encData ++ encNat k).length hlab_le
  have hF := fuelVec_length_eq (D.encData ++ encNat k)
  have h10 : 10 * D.labW ≤ (fuelVec (D.encData ++ encNat k)).length := by
    rw [hF]; exact hbounds.1
  have hwires : 1 + 10 * D.labW ≤ (fuelVec (D.encData ++ encNat k)).length := by
    rw [hF]; exact hbounds.2.1
  have h4 : 4 ≤ (fuelVec (D.encData ++ encNat k)).length := by
    rw [hF]; exact hbounds.2.2.2.2.1
  have hlen_le : (splitInCirc D).length ≤ (fuelVec (D.encData ++ encNat k)).length := by
    have hl : (splitInCirc D).length ≤ 25 * (splitInRev D).length := compileRev_length_le _
    have hr : (splitInRev D).length = 3 * (10 * D.labW) + 1 := by
      simp [splitInRev, shiftUpAux_length]
    rw [hF]
    exact hl.trans ((Nat.mul_le_mul_left 25 hr.le).trans hbounds.2.2.2.2.2.1)
  have hraw : splitInRawLayer (fuelIdx (D.encData ++ encNat k)) (labWRaw (D.encData ++ encNat k)) =
      (splitInCirc D).map toRawInstr := by
    unfold splitInRawLayer rangeFuel splitInCirc splitInRev
    rw [hlab]
    change (((List.range (fuelVec (D.encData ++ encNat k)).length).filter
        (fun j => decide (j < 10 * D.labW))).reverse).flatMap (fun j => rawSwap j (j + 1)) ++
      rawCcx 1 (1 + 7 * D.labW) 0 = _
    rw [filter_range_lt_eq h10, compileRev_append, List.map_append, shiftUpAux_toRaw]
    congr 1
  unfold splitInBuilder
  rw [hraw, hlab]
  change encNatFuel (List.range (fuelVec (D.encData ++ encNat k)).length) (1 + 10 * D.labW) ++
      encRawLayerFuel (List.range (fuelVec (D.encData ++ encNat k)).length) ((splitInCirc D).map toRawInstr) = _
  rw [encNatFuel_eq hwires, encRawLayerFuel_eq h4 hwires _ hlen_le]

lemma mergeOutBuilder_spec (D : FieldData) (k : ℕ) :
    mergeOutBuilder (D.encData ++ encNat k) =
      encNat (1 + 9 * D.labW) ++ encLayer (mergeOutCirc D) := by
  have hlab : labWRaw (D.encData ++ encNat k) = D.labW := labWRaw_encData D k
  have hlab_le : D.labW ≤ 2 * (D.encData ++ encNat k).length ^ 2 :=
    (labW_le_two_encData_sq D).trans (by
      have hlen : D.encData.length ≤ (D.encData ++ encNat k).length := by simp
      nlinarith)
  have hbounds := fuel_bounds_of_labW_le D.labW (D.encData ++ encNat k).length hlab_le
  have hF := fuelVec_length_eq (D.encData ++ encNat k)
  have h9 : 9 * D.labW ≤ (fuelVec (D.encData ++ encNat k)).length := by
    rw [hF]; exact hbounds.2.2.1
  have hwires : 1 + 9 * D.labW ≤ (fuelVec (D.encData ++ encNat k)).length := by
    rw [hF]; exact hbounds.2.2.2.1
  have h4 : 4 ≤ (fuelVec (D.encData ++ encNat k)).length := by
    rw [hF]; exact hbounds.2.2.2.2.1
  have hlen_le : (mergeOutCirc D).length ≤ (fuelVec (D.encData ++ encNat k)).length := by
    have hl : (mergeOutCirc D).length ≤ 25 * (mergeOutRev D).length := compileRev_length_le _
    have hr : (mergeOutRev D).length = 1 + 3 * (9 * D.labW) := by
      simp [mergeOutRev, shiftUpAux_length]
      omega
    rw [hF]
    exact hl.trans ((Nat.mul_le_mul_left 25 hr.le).trans hbounds.2.2.2.2.2.2)
  have hraw : mergeOutRawLayer (fuelIdx (D.encData ++ encNat k)) (labWRaw (D.encData ++ encNat k)) =
      (mergeOutCirc D).map toRawInstr := by
    unfold mergeOutRawLayer rangeFuel mergeOutCirc mergeOutRev
    rw [hlab]
    change rawCcx 1 (1 + 6 * D.labW) 0 ++
      ((List.range (fuelVec (D.encData ++ encNat k)).length).filter
        (fun j => decide (j < 9 * D.labW))).flatMap (fun j => rawSwap j (j + 1)) = _
    rw [filter_range_lt_eq h9, compileRev_append, List.map_append, shiftUpAux_rev_toRaw]
    congr 1
  unfold mergeOutBuilder
  rw [hraw, hlab]
  change encNatFuel (List.range (fuelVec (D.encData ++ encNat k)).length) (1 + 9 * D.labW) ++
      encRawLayerFuel (List.range (fuelVec (D.encData ++ encNat k)).length) ((mergeOutCirc D).map toRawInstr) = _
  rw [encNatFuel_eq hwires, encRawLayerFuel_eq h4 hwires _ hlen_le]

lemma implements_splitIn (D : FieldData) (k : ℕ) :
    Implements (circUnitary (splitInCirc D))
      (fun x : InReg D => padTo (1 + 10 * D.labW) (inCodeA D x))
      (fun y : InRegNonHard D ⊕ InRegHard D =>
        padTo (1 + 10 * D.labW)
          (sumCode (fun z : InRegNonHard D => inCodeA D z.1)
            (fun z : InRegHard D => inCodeA D z.1) y))
      (permMat (splitInA D)) ((1 / 2 : ℝ) ^ k) := by
  rw [splitInCirc, circUnitary_compileRev]
  convert implements_of_act_ket_perm (permMat (evalRev (splitInRev D)))
    (fun x : InReg D => padTo (1 + 10 * D.labW) (inCodeA D x))
    (fun y : InRegNonHard D ⊕ InRegHard D =>
      padTo (1 + 10 * D.labW)
        (sumCode (fun z : InRegNonHard D => inCodeA D z.1)
          (fun z : InRegHard D => inCodeA D z.1) y))
    (splitInA D)
    (fun x => by simpa [splitInCirc, circUnitary_compileRev] using act_splitInCirc D x)
    ((1 / 2 : ℝ) ^ k) (by positivity)

lemma implements_mergeOut (D : FieldData) (k : ℕ) :
    Implements (circUnitary (mergeOutCirc D))
      (fun s : OutRegNonHard D ⊕ OutRegHard D =>
        padTo (1 + 9 * D.labW)
          (sumCode (fun y : OutRegNonHard D => outCodeA D y.1)
            (fun y : OutRegHard D => outCodeA D y.1) s))
      (fun y : OutReg D => padTo (1 + 9 * D.labW) (outCodeA D y))
      (permMat (mergeOutA D)) ((1 / 2 : ℝ) ^ k) := by
  rw [mergeOutCirc, circUnitary_compileRev]
  convert implements_of_act_ket_perm (permMat (evalRev (mergeOutRev D)))
    (fun s : OutRegNonHard D ⊕ OutRegHard D =>
      padTo (1 + 9 * D.labW)
        (sumCode (fun y : OutRegNonHard D => outCodeA D y.1)
          (fun y : OutRegHard D => outCodeA D y.1) s))
    (fun y : OutReg D => padTo (1 + 9 * D.labW) (outCodeA D y))
    (mergeOutA D)
    (fun s => by simpa [mergeOutCirc, circUnitary_compileRev] using act_mergeOutCirc D s)
    ((1 / 2 : ℝ) ^ k) (by positivity)

end GL2QFT_TotalASplitMerge_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates
  QAlgorithms QAlgorithms.Complexity GL2QFT_TotalASplitMerge_Aux in
theorem solution :
    UniformlyImplementsOn (fun D => 2 < D.q) (fun D => inCodeA D)
      (fun D => sumCode (fun x : InRegNonHard D => inCodeA D x.1) (fun x : InRegHard D => inCodeA D x.1))
      (fun D => permMat (splitInA D)) ∧
    UniformlyImplementsOn (fun D => 2 < D.q)
      (fun D => sumCode (fun y : OutRegNonHard D => outCodeA D y.1) (fun y : OutRegHard D => outCodeA D y.1))
      (fun D => outCodeA D) (fun D => permMat (mergeOutA D)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨fun D _ => 1 + 10 * D.labW, fun D _ => splitInCirc D, splitInBuilder, 12,
      polyTime_of_automatic_str poly_splitInBuilder, ?_, ?_, ?_⟩
    · intro D _ k
      exact splitInBuilder_spec D k
    · intro D _ k
      have hl : (splitInCirc D).length ≤ 25 * (splitInRev D).length := compileRev_length_le _
      have hr : (splitInRev D).length = 3 * (10 * D.labW) + 1 := by
        simp [splitInRev, shiftUpAux_length]
      have hlab := labW_le_two_log2_q_add_two D
      have hpow : 2 ^ 11 ≤ (Nat.log 2 D.q + k + 2) ^ 11 :=
        Nat.pow_le_pow_left (by omega) 11
      have hlen : (splitInCirc D).length ≤ 12 * 2 ^ 11 * (Nat.log 2 D.q + k + 2) := by
        norm_num; omega
      have hmul : 12 * 2 ^ 11 * (Nat.log 2 D.q + k + 2) ≤
          12 * (Nat.log 2 D.q + k + 2) ^ 11 * (Nat.log 2 D.q + k + 2) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 12 hpow)
      calc (splitInCirc D).length
          ≤ 12 * 2 ^ 11 * (Nat.log 2 D.q + k + 2) := hlen
        _ ≤ 12 * (Nat.log 2 D.q + k + 2) ^ 11 * (Nat.log 2 D.q + k + 2) := hmul
        _ = 12 * (Nat.log 2 D.q + k + 2) ^ 12 := by ring
    · intro D _ k
      refine ⟨by dsimp only; omega, by dsimp only; rw [Nat.max_self], ?_⟩
      convert implements_splitIn D k
  · refine ⟨fun D _ => 1 + 9 * D.labW, fun D _ => mergeOutCirc D, mergeOutBuilder, 12,
      polyTime_of_automatic_str poly_mergeOutBuilder, ?_, ?_, ?_⟩
    · intro D _ k
      exact mergeOutBuilder_spec D k
    · intro D _ k
      have hl : (mergeOutCirc D).length ≤ 25 * (mergeOutRev D).length := compileRev_length_le _
      have hr : (mergeOutRev D).length = 1 + 3 * (9 * D.labW) := by
        simp [mergeOutRev, shiftUpAux_length]
        omega
      have hlab := labW_le_two_log2_q_add_two D
      have hpow : 2 ^ 11 ≤ (Nat.log 2 D.q + k + 2) ^ 11 :=
        Nat.pow_le_pow_left (by omega) 11
      have hlen : (mergeOutCirc D).length ≤ 12 * 2 ^ 11 * (Nat.log 2 D.q + k + 2) := by
        norm_num; omega
      have hmul : 12 * 2 ^ 11 * (Nat.log 2 D.q + k + 2) ≤
          12 * (Nat.log 2 D.q + k + 2) ^ 11 * (Nat.log 2 D.q + k + 2) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 12 hpow)
      calc (mergeOutCirc D).length
          ≤ 12 * 2 ^ 11 * (Nat.log 2 D.q + k + 2) := hlen
        _ ≤ 12 * (Nat.log 2 D.q + k + 2) ^ 11 * (Nat.log 2 D.q + k + 2) := hmul
        _ = 12 * (Nat.log 2 D.q + k + 2) ^ 12 := by ring
    · intro D _ k
      refine ⟨by dsimp only; rw [Nat.max_self], by dsimp only; omega, ?_⟩
      convert implements_mergeOut D k
