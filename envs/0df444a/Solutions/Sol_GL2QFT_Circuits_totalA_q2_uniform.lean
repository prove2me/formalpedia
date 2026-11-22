-- Prove2me | solution 1 for GL2QFT.Circuits.totalA_q2_uniform
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T08:45:27.576342+00:00
-- url     : https://prove2.me/submissions/895517da-5985-4eeb-810a-b5fbc749602f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GL2QFT_Circuits_Leaves
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Theorems.Thm_GL2QFT_Circuits_A70_small_blocks
import Theorems.Thm_GL2QFT_Circuits_sk_uniform_u2
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_branch
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_seq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_eq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_mono

set_option autoImplicit false

noncomputable section

open Classical

namespace GL2QFT_TotalAQ2_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.Supplement GL2QFT.Supplement.TotalA
  QAlgorithms QAlgorithms.Complexity QAlgorithms.LocalHamiltonian
open OAI.MetricKMedian.Binary
open Automatic

/-! ### Section 1: Elementary quantum gates, `ccx3`, and reversible gates -/

@[simp] lemma wire1_apply {n : ℕ} (i : Fin n) (x : Fin 1) : wire1 i x = i := rfl
@[simp] lemma wire2_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j) : wire2 i j hij 0 = i := rfl
@[simp] lemma wire2_one {n : ℕ} (i j : Fin n) (hij : i ≠ j) : wire2 i j hij 1 = j := rfl

lemma ket_apply {ι : Type} [DecidableEq ι] (i j : ι) :
    (ket i : EuclideanSpace ℂ ι) j = if j = i then 1 else 0 := by
  simp [ket, PiLp.single_apply]

lemma act_add {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) :
    act M (u + v) = act M u + act M v := by
  apply WithLp.ofLp_injective; funext y; simp [act, Matrix.mulVec_add]

lemma act_smul {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (c : ℂ) (u : EuclideanSpace ℂ ι) :
    act M (c • u) = c • act M u := by
  apply WithLp.ofLp_injective; funext y; simp [act, Matrix.mulVec_smul]

lemma act_sum {ι α : Type} [Fintype ι] (M : Matrix ι ι ℂ) (s : Finset α)
    (v : α → EuclideanSpace ℂ ι) :
    act M (∑ a ∈ s, v a) = ∑ a ∈ s, act M (v a) := by
  induction s using Finset.induction_on with
  | empty => apply WithLp.ofLp_injective; funext y; simp [act, Matrix.mulVec_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

lemma ofLp_sum {ι α : Type} [Fintype ι] (s : Finset α) (f : α → EuclideanSpace ℂ ι) :
    (∑ a ∈ s, f a).ofLp = ∑ a ∈ s, (f a).ofLp := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

lemma act_ket {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (q : ι) :
    act M (ket q) = WithLp.toLp 2 (fun y => M y q) := by
  apply WithLp.ofLp_injective; funext y
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
  apply WithLp.ofLp_injective; simp [act, Matrix.mulVec_mulVec]

lemma act_permMat {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ι) (q : ι) :
    act (permMat f) (ket q) = ket (f q) := by
  apply WithLp.ofLp_injective; funext y; simp [act_ket, permMat, ket_apply]

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
  unfold embedOp Gate.ofMatrix1; rw [Matrix.of_apply]
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
  unfold embedOp Gate.ofMatrix2; rw [Matrix.of_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range (wire2 i j hij) → y a = z a) ↔
      (∀ a : Fin n, a ≠ i → a ≠ j → y a = z a) := by
    constructor
    · intro h a hai haj; apply h a; rintro ⟨b, hb⟩; fin_cases b <;> [exact hai hb.symm; exact haj hb.symm]
    · intro h a ha; exact h a (fun heq => ha ⟨0, heq.symm⟩) (fun heq => ha ⟨1, heq.symm⟩)
  by_cases h : ∀ a : Fin n, a ≠ i → a ≠ j → y a = z a
  · rw [if_pos (hiff.mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

lemma instr_x_unitary {n : ℕ} (i : Fin n) :
    circUnitary [.x i] = permMat (fun q : Qubits n => Function.update q i (!q i)) := by
  ext y z
  simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one, instrApp]
  rw [embedOp_wire1]; simp only [pauliX, permMat, Matrix.of_apply]
  by_cases hy : y = Function.update z i (!z i)
  · subst hy; rw [if_pos rfl, if_pos (fun a ha => by simp [ha])]; cases hzi : z i <;> simp
  · rw [if_neg hy]
    by_cases h1 : ∀ a : Fin n, a ≠ i → y a = z a
    · rw [if_pos h1]
      by_cases h2 : y i = z i
      · rw [if_pos h2]
      · exfalso; apply hy; funext a; by_cases hai : a = i
        · subst hai; cases hza : z a <;> cases hya : y a <;> simp_all
        · simp [hai, h1 a hai]
    · rw [if_neg h1]

lemma instr_cnot_unitary {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    circUnitary [.cnot i j hij] =
      permMat (fun q : Qubits n => Function.update q j (xor (q j) (q i))) := by
  ext y z
  simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one, instrApp]
  rw [embedOp_wire2]; simp only [cnot, permMat, Matrix.of_apply]
  by_cases hy : y = Function.update z j (xor (z j) (z i))
  · subst hy; rw [if_pos rfl, if_pos (fun a _ haj => by simp [haj])]; simp [hij]
  · rw [if_neg hy]
    by_cases h1 : ∀ a : Fin n, a ≠ i → a ≠ j → y a = z a
    · rw [if_pos h1]
      by_cases h2 : y i = z i ∧ y j = xor (z j) (z i)
      · exfalso; apply hy; funext a; by_cases haj : a = j
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
  rw [embedOp_wire1]; simp only [phaseS, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz; rw [if_pos rfl, if_pos (fun _ _ => rfl), if_pos rfl]
  · rw [if_neg hyz]
    by_cases h1 : ∀ a : Fin n, a ≠ i → y a = z a
    · rw [if_pos h1]
      have hne : y i ≠ z i := fun heq => hyz (funext fun a => by
        by_cases hai : a = i
        · subst hai; exact heq
        · exact h1 a hai)
      rw [if_neg hne]
    · rw [if_neg h1]

lemma instr_t_unitary {n : ℕ} (i : Fin n) :
    circUnitary [.t i] =
      Matrix.diagonal (fun q : Qubits n => if q i then Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  ext y z
  simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one, instrApp]
  rw [embedOp_wire1]; simp only [gateT, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz; rw [if_pos rfl, if_pos (fun _ _ => rfl), if_pos rfl]
  · rw [if_neg hyz]
    by_cases h1 : ∀ a : Fin n, a ≠ i → y a = z a
    · rw [if_pos h1]
      have hne : y i ≠ z i := fun heq => hyz (funext fun a => by
        by_cases hai : a = i
        · subst hai; exact heq
        · exact h1 a hai)
      rw [if_neg hne]
    · rw [if_neg h1]

lemma act_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (q : ι) :
    act (Matrix.diagonal d) (ket q) = d q • ket q := by
  apply WithLp.ofLp_injective; funext y
  by_cases hy : y = q
  · subst hy; simp [act_ket, ket_apply]
  · simp [act_ket, ket_apply, hy]

lemma act_h_ket {n : ℕ} (i : Fin n) (q : Qubits n) :
    act (circUnitary [.h i]) (ket q) =
      ((Real.sqrt 2)⁻¹ : ℂ) •
        (ket (Function.update q i false) +
          (if q i then (-1 : ℂ) else 1) • ket (Function.update q i true)) := by
  apply WithLp.ofLp_injective; funext y
  simp only [act_ket, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, ket_apply]
  simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one, instrApp]
  rw [embedOp_wire1]; simp only [hadamard, Matrix.of_apply]
  by_cases hother : ∀ a : Fin n, a ≠ i → y a = q a
  · rw [if_pos hother]
    have hy_false : y = Function.update q i false ↔ y i = false :=
      ⟨fun h => by simp [h], fun h => funext fun a => by
        by_cases ha : a = i
        · subst ha; simp [h]
        · simp [ha, hother a ha]⟩
    have hy_true : y = Function.update q i true ↔ y i = true :=
      ⟨fun h => by simp [h], fun h => funext fun a => by
        by_cases ha : a = i
        · subst ha; simp [h]
        · simp [ha, hother a ha]⟩
    cases hyi : y i
    · rw [if_pos (hy_false.mpr hyi),
        if_neg (show y ≠ Function.update q i true from fun h => by
          have := hy_true.mp h; rw [hyi] at this; exact Bool.false_ne_true this)]
      cases hqi : q i <;> simp
    · rw [if_neg (show y ≠ Function.update q i false from fun h => by
          have := hy_false.mp h; rw [hyi] at this; exact Bool.false_ne_true this.symm),
        if_pos (hy_true.mpr hyi)]
      cases hqi : q i <;> simp
  · rw [if_neg hother]
    rw [if_neg (show y ≠ Function.update q i false from fun h => hother fun a hai => by simp [h, hai]),
      if_neg (show y ≠ Function.update q i true from fun h => hother fun a hai => by simp [h, hai])]
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
  rw [h]; simp only [circUnitary_append, act_mul, act_s_ket, act_t_ket, act_smul, smul_smul]
  cases q i
  · simp
  · simp only [↓reduceIte]; congr 1
    calc Complex.I * Complex.I * Complex.I * Complex.exp (Complex.I * ↑Real.pi / 4)
        = (Complex.I * Complex.I) * Complex.I * Complex.exp (Complex.I * ↑Real.pi / 4) := by ring
      _ = (-1) * Complex.I * Complex.exp (Complex.I * ↑Real.pi / 4) := by rw [Complex.I_mul_I]
      _ = -Complex.I * Complex.exp (Complex.I * ↑Real.pi / 4) := by ring

lemma omega_sq :
    Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4) = Complex.I := by
  rw [← Complex.exp_add, show Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4 = (Real.pi / 2 : ℂ) * Complex.I by ring,
    Complex.exp_pi_div_two_mul_I]

lemma sqrt2_inv_sq : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = (2 : ℂ)⁻¹ := by
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  simpa using congrArg (fun r : ℝ => (r : ℂ)) hr

def q3 (a b c : Bool) : Qubits 3 | 0 => a | 1 => b | 2 => c
@[simp] lemma q3_0 (a b c : Bool) : q3 a b c 0 = a := rfl
@[simp] lemma q3_1 (a b c : Bool) : q3 a b c 1 = b := rfl
@[simp] lemma q3_2 (a b c : Bool) : q3 a b c 2 = c := rfl
lemma q3_eq_iff (q : Qubits 3) : q = q3 (q 0) (q 1) (q 2) := by ext i; fin_cases i <;> rfl
lemma update_q3_2 (a b c x : Bool) : Function.update (q3 a b c) 2 x = q3 a b x := by ext i; fin_cases i <;> rfl
lemma update_q3_1 (a b c x : Bool) : Function.update (q3 a b c) 1 x = q3 a x c := by ext i; fin_cases i <;> rfl

def ket3 (a b : Bool) (α β : ℂ) : EuclideanSpace ℂ (Qubits 3) :=
  α • ket (q3 a b false) + β • ket (q3 a b true)

lemma ket3_h2 (a b : Bool) (α β : ℂ) :
    act (circUnitary [.h 2]) (ket3 a b α β) =
      ket3 a b (((Real.sqrt 2)⁻¹ : ℂ) * (α + β)) (((Real.sqrt 2)⁻¹ : ℂ) * (α - β)) := by
  simp only [ket3, act_add, act_smul, act_h_ket, q3_2, update_q3_2, Bool.false_eq_true, ↓reduceIte,
    one_smul, smul_add, smul_smul]
  rw [add_add_add_comm]; congr 1 <;> [rw [← add_smul]; rw [← add_smul]] <;> [congr 1; congr 1] <;> ring

lemma ket3_cnot12 (a b : Bool) (α β : ℂ) :
    act (circUnitary [.cnot 1 2 (by decide)]) (ket3 a b α β) =
      if b then ket3 a b β α else ket3 a b α β := by
  simp only [ket3, act_add, act_smul, act_cnot_ket, q3_1, q3_2, update_q3_2]; cases b <;> simp [add_comm]

lemma ket3_cnot02 (a b : Bool) (α β : ℂ) :
    act (circUnitary [.cnot 0 2 (by decide)]) (ket3 a b α β) =
      if a then ket3 a b β α else ket3 a b α β := by
  simp only [ket3, act_add, act_smul, act_cnot_ket, q3_0, q3_2, update_q3_2]; cases a <;> simp [add_comm]

lemma ket3_t2 (a b : Bool) (α β : ℂ) :
    act (circUnitary [.t 2]) (ket3 a b α β) =
      ket3 a b α (Complex.exp (Complex.I * Real.pi / 4) * β) := by
  simp only [ket3, act_add, act_smul, act_t_ket, q3_2, Bool.false_eq_true, ↓reduceIte, one_smul, smul_smul]
  rw [mul_comm β _]

lemma ket3_tdg2 (a b : Bool) (α β : ℂ) :
    act (circUnitary (tdg 2)) (ket3 a b α β) =
      ket3 a b α ((-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * β) := by
  simp only [ket3, act_add, act_smul, act_tdg_ket, q3_2, Bool.false_eq_true, ↓reduceIte, one_smul, smul_smul]
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
  have hω2 : ∀ z : ℂ, Complex.exp (Complex.I * Real.pi / 4) * (Complex.exp (Complex.I * Real.pi / 4) * z) = Complex.I * z := fun z => by
    rw [← mul_assoc, omega_sq]
  have hωω' : ∀ z : ℂ, Complex.exp (Complex.I * Real.pi / 4) * ((-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * z) = z := fun z => by
    calc Complex.exp (Complex.I * Real.pi / 4) * ((-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * z)
        = (-Complex.I * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4))) * z := by ring
      _ = (-Complex.I * Complex.I) * z := by rw [omega_sq]
      _ = z := by simp [Complex.I_mul_I]
  have hω'ω : ∀ z : ℂ, (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * (Complex.exp (Complex.I * Real.pi / 4) * z) = z := fun z => by
    calc (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * (Complex.exp (Complex.I * Real.pi / 4) * z)
        = (-Complex.I * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4))) * z := by ring
      _ = (-Complex.I * Complex.I) * z := by rw [omega_sq]
      _ = z := by simp [Complex.I_mul_I]
  have hω'2 : ∀ z : ℂ, (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * ((-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * z) = -Complex.I * z := fun z => by
    calc (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * ((-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * z)
        = ((Complex.I * Complex.I) * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4))) * z := by ring
      _ = ((-1) * Complex.I) * z := by rw [Complex.I_mul_I, omega_sq]
      _ = -Complex.I * z := by ring
  have hsplit : ccx3Mid =
      [.h 2] ++ [.cnot 1 2 (by decide)] ++ tdg 2 ++ [.cnot 0 2 (by decide)] ++
      [.t 2] ++ [.cnot 1 2 (by decide)] ++ tdg 2 ++ [.cnot 0 2 (by decide)] ++
      [.t 2] ++ [.h 2] := by simp [ccx3Mid, List.append_assoc]
  set α₀ : ℂ := if c then 0 else 1
  set β₀ : ℂ := if c then 1 else 0
  have hket : ket (q3 a b c) = ket3 a b α₀ β₀ := by cases c <;> simp [ket3, α₀, β₀]
  rw [hsplit, hket]; simp only [circUnitary_append, act_mul]
  change act (circUnitary [.h 2]) (act (circUnitary [.t 2]) (act (circUnitary [.cnot 0 2 (by decide)])
    (act (circUnitary (tdg 2)) (act (circUnitary [.cnot 1 2 (by decide)]) (act (circUnitary [.t 2])
      (act (circUnitary [.cnot 0 2 (by decide)]) (act (circUnitary (tdg 2))
        (act (circUnitary [.cnot 1 2 (by decide)]) (act (circUnitary [.h 2])
          (ket3 a b α₀ β₀)))))))))) = _
  rw [ket3_h2, ket3_cnot12]
  have h1 : s * (s * (α₀ + β₀) + s * (α₀ - β₀)) = α₀ := by
    calc s * (s * (α₀ + β₀) + s * (α₀ - β₀)) = (s * s) * (2 * α₀) := by ring
      _ = (2 : ℂ)⁻¹ * (2 * α₀) := by rw [hs2]
      _ = α₀ := by ring
  have h2 : s * (s * (α₀ + β₀) - s * (α₀ - β₀)) = β₀ := by
    calc s * (s * (α₀ + β₀) - s * (α₀ - β₀)) = (s * s) * (2 * β₀) := by ring
      _ = (2 : ℂ)⁻¹ * (2 * β₀) := by rw [hs2]
      _ = β₀ := by ring
  cases b
  · rw [if_neg Bool.false_ne_true, ket3_tdg2, ket3_cnot02]
    cases a
    · rw [if_neg Bool.false_ne_true, ket3_t2, hωω', ket3_cnot12, if_neg Bool.false_ne_true,
        ket3_tdg2, ket3_cnot02, if_neg Bool.false_ne_true, ket3_t2, hωω', ket3_h2]
      change ket3 false false (s * (s * (α₀ + β₀) + s * (α₀ - β₀))) (s * (s * (α₀ + β₀) - s * (α₀ - β₀))) = _
      rw [h1, h2, ← hket]; simp
    · rw [if_pos rfl, ket3_t2, ket3_cnot12, if_neg Bool.false_ne_true, ket3_tdg2, hω'ω,
        ket3_cnot02, if_pos rfl, ket3_t2, hωω', ket3_h2]
      change ket3 true false (s * (s * (α₀ + β₀) + s * (α₀ - β₀))) (s * (s * (α₀ + β₀) - s * (α₀ - β₀))) = _
      rw [h1, h2, ← hket]; simp
  · rw [if_pos rfl, ket3_tdg2, ket3_cnot02]
    cases a
    · rw [if_neg Bool.false_ne_true, ket3_t2, hωω', ket3_cnot12, if_pos rfl, ket3_tdg2,
        ket3_cnot02, if_neg Bool.false_ne_true, ket3_t2, hωω', ket3_h2]
      change ket3 false true (s * (s * (α₀ + β₀) + s * (α₀ - β₀))) (s * (s * (α₀ + β₀) - s * (α₀ - β₀))) = _
      rw [h1, h2, ← hket]; simp
    · rw [if_pos rfl, ket3_t2, ket3_cnot12, if_pos rfl, ket3_tdg2, hω'2, ket3_cnot02,
        if_pos rfl, ket3_t2, hω2, ket3_h2]
      have h1' : s * (-Complex.I * (s * (α₀ + β₀)) + Complex.I * (s * (α₀ - β₀))) = -Complex.I * β₀ := by
        calc s * (-Complex.I * (s * (α₀ + β₀)) + Complex.I * (s * (α₀ - β₀)))
            = (s * s) * (-2 * Complex.I * β₀) := by ring
          _ = (2 : ℂ)⁻¹ * (-2 * Complex.I * β₀) := by rw [hs2]
          _ = -Complex.I * β₀ := by ring
      have h2' : s * (-Complex.I * (s * (α₀ + β₀)) - Complex.I * (s * (α₀ - β₀))) = -Complex.I * α₀ := by
        calc s * (-Complex.I * (s * (α₀ + β₀)) - Complex.I * (s * (α₀ - β₀)))
            = (s * s) * (-2 * Complex.I * α₀) := by ring
          _ = (2 : ℂ)⁻¹ * (-2 * Complex.I * α₀) := by rw [hs2]
          _ = -Complex.I * α₀ := by ring
      change ket3 true true (s * (-Complex.I * (s * (α₀ + β₀)) + Complex.I * (s * (α₀ - β₀))))
        (s * (-Complex.I * (s * (α₀ + β₀)) - Complex.I * (s * (α₀ - β₀)))) = _
      rw [h1', h2']; cases c <;> simp [ket3, α₀, β₀]

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
  rw [hsplit]; simp only [circUnitary_append, act_mul, act_ccx3Mid_ket]
  change act (circUnitary [.cnot 0 1 (by decide)]) (act (circUnitary (tdg 1))
    (act (circUnitary [.t 0]) (act (circUnitary [.cnot 0 1 (by decide)])
      (act (circUnitary [.t 1]) ((if q 0 && q 1 then -Complex.I else 1) •
        ket (q3 (q 0) (q 1) (xor (q 2) (q 0 && q 1)))))))) = _
  have hphase1 : Complex.exp (Complex.I * Real.pi / 4) * (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) = 1 := by
    calc Complex.exp (Complex.I * Real.pi / 4) * (-Complex.I * Complex.exp (Complex.I * Real.pi / 4))
        = -Complex.I * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4)) := by ring
      _ = -Complex.I * Complex.I := by rw [omega_sq]
      _ = 1 := by simp [Complex.I_mul_I]
  have hphase2 : (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * Complex.exp (Complex.I * Real.pi / 4) = 1 := by
    calc (-Complex.I * Complex.exp (Complex.I * Real.pi / 4)) * Complex.exp (Complex.I * Real.pi / 4)
        = -Complex.I * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4)) := by ring
      _ = -Complex.I * Complex.I := by rw [omega_sq]
      _ = 1 := by simp [Complex.I_mul_I]
  cases h0 : q 0 <;> cases h1 : q 1
  · simp only [act_t_ket, act_cnot_ket, act_tdg_ket, q3_0, q3_1, update_q3_1,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.xor_false, one_smul]
  · simp only [act_smul, act_t_ket, act_cnot_ket, act_tdg_ket, q3_0, q3_1, update_q3_1,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.xor_false, one_smul, smul_smul]
    rw [hphase1]; simp [one_smul]
  · simp only [act_smul, act_t_ket, act_cnot_ket, act_tdg_ket, q3_0, q3_1, update_q3_1,
      Bool.true_and, Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true, one_smul, smul_smul]
    rw [hphase1]; simp [one_smul]
  · simp only [act_smul, act_t_ket, act_cnot_ket, act_tdg_ket, q3_0, q3_1, update_q3_1,
      Bool.true_and, ↓reduceIte, Bool.xor_true, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, smul_smul, mul_one]
    rw [hphase2]; simp [one_smul]

lemma circUnitary_ccx3 :
    circUnitary ccx3 =
      permMat (fun q : Qubits 3 => Function.update q 2 (xor (q 2) (q 0 && q 1))) := by
  apply matrix_eq_of_act_ket; intro q; rw [act_ccx3_ket, act_permMat]

lemma embedOp_mul {k n : ℕ} (A B : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  ext y z; simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    let agree (u : Qubits n) : Prop := ∀ a : Fin n, a ∉ Set.range w → y a = u a
    let mkU (v : Qubits k) : Qubits n := fun a => if h : ∃ i, w i = a then v h.choose else y a
    have hmkU_w : ∀ v i, mkU v (w i) = v i := fun v i => by
      have hex : ∃ j, w j = w i := ⟨i, rfl⟩
      simp only [mkU, dif_pos hex]; congr 1; exact w.injective hex.choose_spec
    have hmkU_off : ∀ v, agree (mkU v) := fun v a ha => by
      simp only [mkU, dif_neg (show ¬ ∃ i, w i = a from fun ⟨i, hi⟩ => ha ⟨i, hi⟩)]
    have hmkU_id : ∀ u, agree u → mkU (fun i => u (w i)) = u := fun u hu => by
      funext a; by_cases hex : ∃ i, w i = a
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
        · rw [if_pos hua, if_pos (fun a ha => (hua a ha).symm.trans (hyz a ha)), if_pos hua]
        · rw [if_neg hua, zero_mul, if_neg hua]
      rw [hrew, ← Finset.sum_filter]
    rw [hsum1]
    refine Finset.sum_nbij' mkU (fun (u : Qubits n) (i : Fin k) => u (w i)) ?_ ?_ ?_ ?_ ?_
    · intro v _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmkU_off v⟩
    · intro u _; exact Finset.mem_univ _
    · intro v _; funext i; exact hmkU_w v i
    · intro u hu; exact hmkU_id u (Finset.mem_filter.mp hu).2
    · intro v _; have hcomp : mkU v ∘ w = v := by funext i; exact hmkU_w v i
      rw [hcomp]
  · rw [if_neg hyz]; symm; refine Finset.sum_eq_zero fun u _ => ?_
    split_ifs with h1 h2
    · exfalso; exact hyz fun a ha => (h1 a ha).trans (h2 a ha)
    · simp
    · simp
    · simp

lemma embedOp_trans {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin m) (e : Fin m ↪ Fin n) :
    embedOp (embedOp M w) e = embedOp M (w.trans e) := by
  ext y z; simp only [embedOp, Matrix.of_apply]
  have hiff : ((∀ a : Fin n, a ∉ Set.range e → y a = z a) ∧
      (∀ b : Fin m, b ∉ Set.range w → y (e b) = z (e b))) ↔
      (∀ a : Fin n, a ∉ Set.range (w.trans e) → y a = z a) := by
    constructor
    · rintro ⟨h1, h2⟩ a ha
      by_cases hae : a ∈ Set.range e
      · rcases hae with ⟨b, rfl⟩; exact h2 b fun ⟨i, hi⟩ => ha ⟨i, by simp [hi]⟩
      · exact h1 a hae
    · intro h
      refine ⟨fun a ha => h a fun ⟨i, hi⟩ => ha ⟨w i, by simpa using hi⟩, ?_⟩
      intro b hb; apply h (e b); rintro ⟨i, hi⟩; exact hb ⟨i, e.injective hi⟩
  have hc1 : (y ∘ e) ∘ w = y ∘ ⇑(w.trans e) := rfl
  have hc2 : (z ∘ e) ∘ w = z ∘ ⇑(w.trans e) := rfl
  by_cases h1 : ∀ a : Fin n, a ∉ Set.range e → y a = z a
  · by_cases h2 : ∀ b : Fin m, b ∉ Set.range w → (y ∘ e) b = (z ∘ e) b
    · rw [if_pos h1, if_pos h2, if_pos (hiff.mp ⟨h1, h2⟩), hc1, hc2]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (hiff.mpr h).2)]
  · rw [if_neg h1, if_neg (fun h => h1 (hiff.mpr h).1)]

lemma instrApp_mapInstr {m n : ℕ} (e : Fin m ↪ Fin n) (ins : Instr m) :
    embedOp (instrApp (mapInstr e ins)).gate.mat (instrApp (mapInstr e ins)).wires =
      embedOp (instrApp ins).gate.mat ((instrApp ins).wires.trans e) := by
  cases ins with
  | h i | s i | t i | x i => simp only [mapInstr, instrApp]; congr 1
  | cnot i j hij => simp only [mapInstr, instrApp]; congr 1; ext a; fin_cases a <;> rfl

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

@[simp] lemma wire3_0 {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : wire3 i j k hij hik hjk 0 = i := rfl
@[simp] lemma wire3_1 {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : wire3 i j k hij hik hjk 1 = j := rfl
@[simp] lemma wire3_2 {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : wire3 i j k hij hik hjk 2 = k := rfl

lemma embedOp_wire3_ccx {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    embedOp (permMat (fun q : Qubits 3 => Function.update q 2 (xor (q 2) (q 0 && q 1))))
        (wire3 i j k hij hik hjk) =
      permMat (fun q : Qubits n => Function.update q k (xor (q k) (q i && q j))) := by
  let e := wire3 i j k hij hik hjk
  ext y z; simp only [embedOp, permMat, Matrix.of_apply]
  by_cases hy : y = Function.update z k (xor (z k) (z i && z j))
  · subst hy
    rw [if_pos rfl, if_pos (fun a ha => by rw [Function.update_of_ne (fun heq => ha ⟨2, by simp [e, heq]⟩)])]
    rw [if_pos (funext fun a => by fin_cases a <;> simp [e, hik, hjk])]
  · rw [if_neg hy]
    by_cases h1 : ∀ a : Fin n, a ∉ Set.range e → y a = z a
    · rw [if_pos h1]
      by_cases h2 : y ∘ e = Function.update (z ∘ e) 2 (xor ((z ∘ e) 2) ((z ∘ e) 0 && (z ∘ e) 1))
      · exfalso; apply hy; funext a
        by_cases hak : a = k
        · subst hak; simpa [e, wire3_0, wire3_1, wire3_2] using congrFun h2 2
        · by_cases hai : a = i
          · subst hai; simpa [e, wire3_0, hak] using congrFun h2 0
          · by_cases haj : a = j
            · subst haj; simpa [e, wire3_1, hak] using congrFun h2 1
            · have ha_range : a ∉ Set.range e := by
                rintro ⟨b, hb⟩; fin_cases b <;> [exact hai (by simpa [e, wire3_0] using hb.symm);
                  exact haj (by simpa [e, wire3_1] using hb.symm); exact hak (by simpa [e, wire3_2] using hb.symm)]
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

def evalRev {n : ℕ} (gs : List (RevGate n)) (q : Qubits n) : Qubits n :=
  gs.foldl (fun s g => g.eval s) q

@[simp] lemma evalRev_nil {n : ℕ} (q : Qubits n) : evalRev [] q = q := rfl
@[simp] lemma evalRev_cons {n : ℕ} (g : RevGate n) (gs : List (RevGate n)) (q : Qubits n) :
    evalRev (g :: gs) q = evalRev gs (g.eval q) := rfl
@[simp] lemma evalRev_append {n : ℕ} (gs₁ gs₂ : List (RevGate n)) (q : Qubits n) :
    evalRev (gs₁ ++ gs₂) q = evalRev gs₂ (evalRev gs₁ q) := by
  simp [evalRev, List.foldl_append]

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
    by_cases h : y = z <;> simp [compileRev, evalRev, circUnitary_nil, permMat, h]
  | cons g gs ih =>
    have hcons : g :: gs = [g] ++ gs := rfl
    rw [hcons, compileRev_append, circUnitary_append, ih]
    have hg : compileRev [g] = g.compile := List.append_nil _
    rw [hg, circUnitary_compile, permMat_mul]
    rfl

lemma compileRev_length_le {n : ℕ} (gs : List (RevGate n)) :
    (compileRev gs).length ≤ gs.length * (ccx3.length + 1) := by
  induction gs with
  | nil => simp [compileRev]
  | cons g gs ih =>
    have hcomp : compileRev (g :: gs) = g.compile ++ compileRev gs := rfl
    rw [hcomp, List.length_append, List.length_cons]
    have hg : g.compile.length ≤ ccx3.length + 1 := by
      cases g with
      | x _ => simp [RevGate.compile]
      | cnot _ _ _ => simp [RevGate.compile]
      | ccx _ _ _ _ _ _ =>
        simp [RevGate.compile, mapCirc, List.length_map]
    rw [Nat.add_mul, one_mul]
    omega

lemma implements_of_act_ket_perm {X Y : Type} [Fintype X] [Fintype Y] {n : ℕ}
    (U : Matrix (Qubits n) (Qubits n) ℂ) (cin : X → Qubits n) (cout : Y → Qubits n)
    (f : X → Y) (h : ∀ x : X, act U (ket (cin x)) = ket (cout (f x))) (ε : ℝ) (hε : 0 ≤ ε) :
    Implements U cin cout (permMat f) ε := by
  intro ψ
  have hembed_in : embedVec cin ψ = ∑ x : X, ψ x • ket (cin x) := by
    apply WithLp.ofLp_injective; funext q; rw [ofLp_sum, Finset.sum_apply]
    simp only [embedVec, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul, ket_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : cin x = q <;> [simp [hx]; simp [hx, Ne.symm hx]]
  have hembed_out : embedVec cout (WithLp.toLp 2 ((permMat f).mulVec (WithLp.ofLp ψ))) =
      ∑ x : X, ψ x • ket (cout (f x)) := by
    apply WithLp.ofLp_injective; funext q; rw [ofLp_sum, Finset.sum_apply]
    simp only [embedVec, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul, ket_apply,
      Matrix.mulVec, dotProduct, permMat, Matrix.of_apply]
    calc (∑ y : Y, if cout y = q then ∑ x : X, (if y = f x then (1 : ℂ) else 0) * ψ x else 0)
        = ∑ y : Y, ∑ x : X, (if cout y = q then if y = f x then ψ x else 0 else 0) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            split_ifs with hy
            · refine Finset.sum_congr rfl fun x _ => ?_; split_ifs <;> simp
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
    refine Finset.sum_congr rfl fun x _ => ?_; rw [act_smul, h x]
  rw [hact, sub_self, norm_zero]
  exact mul_nonneg hε (norm_nonneg ψ)

lemma norm_mulVec_le_of_iso {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    (M : Matrix Y X ℂ) (hM : M.conjTranspose * M = 1) (ψ : EuclideanSpace ℂ X) :
    ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))‖ ≤ ‖ψ‖ := by
  have hnorm_sq : ∀ {ι : Type} [Fintype ι] (v : ι → ℂ),
      ((∑ i : ι, ‖v i‖ ^ 2 : ℝ) : ℂ) = ∑ i : ι, star (v i) * v i := by
    intro ι _ v; push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
      RCLike.star_def, mul_comm]
  have hlhs_c : ((‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))‖ ^ 2 : ℝ) : ℂ) =
      ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, hnorm_sq, hnorm_sq]
    simp_rw [Matrix.mulVec, dotProduct, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    rw [Finset.sum_comm]
    have hx : ∀ x₂ : X, (∑ y : Y, star (ψ x₁) * star (M y x₁) * (M y x₂ * ψ x₂)) =
        if x₁ = x₂ then star (ψ x₁) * ψ x₁ else 0 := by
      intro x₂
      have hm := congrArg (fun A : Matrix X X ℂ => A x₁ x₂) hM
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
      calc (∑ y : Y, star (ψ x₁) * star (M y x₁) * (M y x₂ * ψ x₂))
          = star (ψ x₁) * (∑ y : Y, star (M y x₁) * M y x₂) * ψ x₂ := by
              simp_rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun y _ => by ring
        _ = star (ψ x₁) * (if x₁ = x₂ then 1 else 0) * ψ x₂ := by rw [hm]
        _ = if x₁ = x₂ then star (ψ x₁) * ψ x₁ else 0 := by
              by_cases h12 : x₁ = x₂ <;> simp [h12]
    simp_rw [hx, Finset.sum_ite_eq, Finset.mem_univ]; simp
  have hlhs_r : ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))‖ ^ 2 = ‖ψ‖ ^ 2 :=
    Complex.ofReal_injective hlhs_c
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]; exact hlhs_r.le

lemma permMat_iso {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (hf : Function.Injective f) :
    (permMat f).conjTranspose * permMat f = 1 := by
  ext x₁ x₂
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permMat, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (f x₁)]
  · by_cases h : x₁ = x₂
    · subst h; simp
    · simp [h, hf.ne h]
  · intro y _ hy; simp [hy]
  · intro hm; exact (hm (Finset.mem_univ (f x₁))).elim

/-! ### Section 2: `Automatic.Poly` dyadic oracle for `U_q` -/

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
        · simp only [Nat.bit, cond_false]; exact Nat.pos_of_ne_zero fun hn => h0 ⟨by omega, rfl⟩
        · simp [Nat.bit]
      | succ k =>
        rw [Nat.add_le_add_iff_right, ih, Nat.pow_succ']
        cases b <;> simp [Nat.bit] <;> omega

lemma bits_length_mono {a b : ℕ} (h : a ≤ b) : a.bits.length ≤ b.bits.length := by
  rw [natBits_length_le_iff]
  exact lt_of_le_of_lt h (natBits_length_le_iff.mp le_rfl)

@[fun_prop] lemma poly_natBits : Automatic.Poly Nat.bits :=
  ⟨BooleanLists.packProgram.recode Nat.bits (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] lemma poly_natBits_comp {α : Type} [Automatic.Coding α] {f : α → ℕ} (hf : Automatic.Poly f) :
    Automatic.Poly (fun x => (f x).bits) := by
  rcases hf with ⟨Pf⟩; rcases poly_natBits with ⟨Pb⟩; exact ⟨(Pf.comp Pb).congr _ (fun _ => rfl)⟩

@[fun_prop] lemma poly_natBodd : Automatic.Poly Nat.bodd := ⟨PolyProgram.natOdd⟩

@[fun_prop] lemma poly_natBodd_comp {α : Type} [Automatic.Coding α] {f : α → ℕ} (hf : Automatic.Poly f) :
    Automatic.Poly (fun x => (f x).bodd) := by
  rcases hf with ⟨Pf⟩; exact ⟨(Pf.comp PolyProgram.natOdd).congr _ (fun _ => rfl)⟩

@[fun_prop] lemma poly_natDiv : Automatic.Poly (fun p : ℕ × ℕ => p.1 / p.2) := ⟨PolyProgram.natDiv⟩

@[fun_prop] lemma poly_natDiv_comp {α : Type} [Automatic.Coding α] {a b : α → ℕ}
    (ha : Automatic.Poly a) (hb : Automatic.Poly b) : Automatic.Poly (fun x => a x / b x) := by
  rcases ha with ⟨Pa⟩; rcases hb with ⟨Pb⟩
  exact ⟨((Pa.fanout Pb).comp PolyProgram.natDiv).congr _ (fun _ => rfl)⟩

@[fun_prop] lemma poly_listReverse {α : Type} [Automatic.Coding α] [Inhabited α] :
    Automatic.Poly (List.reverse : List α → List α) :=
  ⟨PolyProgram.listReverse Automatic.enc default⟩

@[fun_prop] lemma poly_listReverse_comp {α β : Type} [Automatic.Coding α] [Automatic.Coding β] [Inhabited β]
    {l : α → List β} (hl : Automatic.Poly l) :
    Automatic.Poly (fun x => (l x).reverse) := by
  rcases hl with ⟨Pl⟩; exact ⟨(Pl.comp (PolyProgram.listReverse Automatic.enc default)).congr _ (fun _ => rfl)⟩

@[fun_prop] lemma poly_list_indices_comp {α β : Type} [Automatic.Coding α] [Automatic.Coding β] [Inhabited β]
    {l : α → List β} (hl : Automatic.Poly l) :
    Automatic.Poly (fun x => List.range (l x).length) := by
  rcases hl with ⟨Pl⟩
  rcases (Automatic.Poly.list_indices : Automatic.Poly fun xs : List β => List.range xs.length) with ⟨Pi⟩
  exact ⟨(Pl.comp Pi).congr _ (fun _ => rfl)⟩

def decodeBits (bs : List Bool) : ℕ :=
  bs.reverse.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0

@[fun_prop] lemma poly_decodeBits : Automatic.Poly decodeBits := by
  have hstep : Automatic.Poly (fun p : ℕ × Bool => 2 * p.1 + if p.2 then 1 else 0) := by fun_prop
  have hfold : Automatic.Poly
      (fun x : List Bool × ℕ => List.foldl (fun acc b => 2 * acc + if b then 1 else 0) x.2 x.1) := by
    rcases hstep with ⟨Ps⟩
    refine ⟨PolyProgram.listFoldLinear Ps false 1 fun b a => ?_⟩
    have hstep_le : (2 * b + if a then 1 else 0).bits.length ≤ b.bits.length + 1 := by
      rw [natBits_length_le_iff, Nat.pow_succ']
      have hb0 := natBits_length_le_iff.mp (le_refl b.bits.length)
      cases a <;> simp <;> omega
    exact hstep_le.trans (by change _ ≤ b.bits.length + 1 * (2 * (encodeBool a).length + 1); omega)
  have hrev : Automatic.Poly (fun bs : List Bool => bs.reverse) := by fun_prop
  have h0 : Automatic.Poly (fun _ : List Bool => (0 : ℕ)) := by fun_prop
  rcases hrev with ⟨Prev⟩; rcases h0 with ⟨P0⟩; rcases hfold with ⟨Pfold⟩
  exact ⟨((Prev.fanout P0).comp Pfold).congr _ (fun _ => rfl)⟩

@[fun_prop] lemma poly_decodeBits_comp {α : Type} [Automatic.Coding α] {bs : α → List Bool} (hbs : Automatic.Poly bs) :
    Automatic.Poly (fun x => decodeBits (bs x)) := by
  rcases hbs with ⟨Pbs⟩; rcases poly_decodeBits with ⟨Pd⟩; exact ⟨(Pbs.comp Pd).congr _ (fun _ => rfl)⟩

lemma decodeBits_bits (n : ℕ) : decodeBits n.bits = n := by
  induction n using Nat.binaryRec with
  | zero => rfl
  | bit b n ih =>
    by_cases h0 : n = 0 ∧ b = false
    · rcases h0 with ⟨rfl, rfl⟩; simp [Nat.bit, decodeBits]
    · have hne : n = 0 → b = true := fun hn => by cases hb : b <;> [exact absurd ⟨hn, hb⟩ h0; rfl]
      simp only [decodeBits, Nat.bits_append_bit n b hne, List.reverse_cons, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      change 2 * decodeBits n.bits + (if b then 1 else 0) = Nat.bit b n
      rw [ih]; cases b <;> simp [Nat.bit]

def prodList (as : List ℕ) : ℕ := as.foldl (· * ·) 1

lemma natBits_mul_length_le (x y : ℕ) :
    (x * y).bits.length ≤ x.bits.length + y.bits.length := by
  rw [natBits_length_le_iff, Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (natBits_length_le_iff.mp le_rfl) (natBits_length_le_iff.mp le_rfl)

@[fun_prop] lemma poly_prodList : Automatic.Poly prodList := by
  have hop : Automatic.Poly (fun p : ℕ × ℕ => p.1 * p.2) := by fun_prop
  have hfold : Automatic.Poly (fun x : List ℕ × ℕ => List.foldl (· * ·) x.2 x.1) := by
    rcases hop with ⟨Pop⟩
    refine ⟨PolyProgram.listFoldLinear Pop 0 1 fun b a => ?_⟩
    exact (natBits_mul_length_le b a).trans (by change _ ≤ b.bits.length + 1 * (2 * a.bits.length + 1); omega)
  have hid : Automatic.Poly (fun as : List ℕ => as) := by fun_prop
  have h1 : Automatic.Poly (fun _ : List ℕ => (1 : ℕ)) := by fun_prop
  rcases hid with ⟨Pid⟩; rcases h1 with ⟨P1⟩; rcases hfold with ⟨Pfold⟩
  exact ⟨((Pid.fanout P1).comp Pfold).congr _ (fun _ => rfl)⟩

@[fun_prop] lemma poly_prodList_comp {α : Type} [Automatic.Coding α] {as : α → List ℕ} (has : Automatic.Poly as) :
    Automatic.Poly (fun x => prodList (as x)) := by
  rcases has with ⟨Pas⟩; rcases poly_prodList with ⟨Pp⟩; exact ⟨(Pas.comp Pp).congr _ (fun _ => rfl)⟩

lemma prodList_replicate (n p : ℕ) : prodList (List.replicate n p) = p ^ n := by
  unfold prodList
  have h : ∀ (acc : ℕ), (List.replicate n p).foldl (· * ·) acc = acc * p ^ n := fun acc => by
    induction n generalizing acc with
    | zero => simp
    | succ n ih => rw [List.replicate_succ, List.foldl_cons, ih, pow_succ', mul_assoc]
  simpa using h 1

lemma encBin_length (m : ℕ) : (encBin m).length = 2 * m.bits.length + 2 := by
  simp only [encBin, List.length_append, List.length_cons, List.length_nil, List.length_flatMap]
  induction m.bits with | nil => simp | cons _ _ ih => simp; omega

lemma flatMap_pair_length (bs : List Bool) :
    (bs.flatMap (fun β => [true, β])).length = 2 * bs.length := by
  induction bs with | nil => simp | cons _ _ ih => simp; omega

lemma flatMap_pair_getElem_even (bs : List Bool) (j : ℕ) (hj : j < bs.length) :
    (bs.flatMap (fun β => [true, β]))[2 * j]'(by rw [flatMap_pair_length]; omega) = true := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons _ _ ih =>
    cases j with
    | zero => simp
    | succ j => simp only [List.flatMap_cons, List.cons_append]; simpa [show 2 * (j + 1) = (2 * j + 1) + 1 by omega] using ih j (by simpa using hj)

lemma flatMap_pair_getElem_odd (bs : List Bool) (j : ℕ) (hj : j < bs.length) :
    (bs.flatMap (fun β => [true, β]))[2 * j + 1]'(by rw [flatMap_pair_length]; omega) = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons _ _ ih =>
    cases j with
    | zero => simp
    | succ j => simp only [List.flatMap_cons, List.cons_append]; simpa [show 2 * (j + 1) + 1 = (2 * j + 1 + 1) + 1 by omega] using ih j (by simpa using hj)

lemma encBin_getElem?_even {m j : ℕ} (hj : j < m.bits.length) :
    (encBin m)[2 * j]? = some true := by
  rw [List.getElem?_eq_getElem (by rw [encBin_length]; omega)]
  simp only [encBin]
  rw [List.getElem_append_left (by rw [flatMap_pair_length]; omega)]
  exact congrArg some (flatMap_pair_getElem_even m.bits j hj)

lemma encBin_getElem?_odd {m j : ℕ} (hj : j < m.bits.length) :
    (encBin m)[2 * j + 1]? = some m.bits[j] := by
  rw [List.getElem?_eq_getElem (by rw [encBin_length]; omega)]
  simp only [encBin]
  rw [List.getElem_append_left (by rw [flatMap_pair_length]; omega)]
  exact congrArg some (flatMap_pair_getElem_odd m.bits j hj)

lemma encBin_getElem?_end (m : ℕ) :
    (encBin m)[2 * m.bits.length]? = some false := by
  simp only [encBin]
  rw [List.getElem?_append_right (by rw [flatMap_pair_length]), flatMap_pair_length, Nat.sub_self]
  rfl

def binEndAfter (xs : List Bool) (start : ℕ) : ℕ :=
  ((List.range xs.length).filter (fun i => decide (start ≤ i) && !Nat.bodd i && !xs[i]?.getD false)).head?.getD 0

@[fun_prop] lemma poly_binEndAfter_pair : Automatic.Poly (fun p : List Bool × ℕ => binEndAfter p.1 p.2) := by
  unfold binEndAfter; fun_prop

@[fun_prop] lemma poly_binEndAfter_comp {α : Type} [Automatic.Coding α] {xs : α → List Bool} {s : α → ℕ}
    (hxs : Automatic.Poly xs) (hs : Automatic.Poly s) : Automatic.Poly (fun x => binEndAfter (xs x) (s x)) := by
  rcases hxs with ⟨Pxs⟩; rcases hs with ⟨Ps⟩; rcases poly_binEndAfter_pair with ⟨Pb⟩
  exact ⟨((Pxs.fanout Ps).comp Pb).congr _ (fun _ => rfl)⟩

def parseBinFrom (xs : List Bool) (start : ℕ) : ℕ :=
  decodeBits
    (((List.range xs.length).filter
      (fun i => decide (start ≤ i) && decide (i < binEndAfter xs start) && Nat.bodd i)).map
      (fun i => xs[i]?.getD false))

@[fun_prop] lemma poly_parseBinFrom_pair : Automatic.Poly (fun p : List Bool × ℕ => parseBinFrom p.1 p.2) := by
  unfold parseBinFrom; fun_prop

@[fun_prop] lemma poly_parseBinFrom_comp {α : Type} [Automatic.Coding α] {xs : α → List Bool} {s : α → ℕ}
    (hxs : Automatic.Poly xs) (hs : Automatic.Poly s) : Automatic.Poly (fun x => parseBinFrom (xs x) (s x)) := by
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
    List.filter_eq_nil_iff.mpr fun i hi => by rw [List.mem_range] at hi; simp [hpre i hi]
  rw [hnil, List.nil_append, List.filter_cons, hpE]; rfl

lemma last?_filter_range {N E : ℕ} (p : ℕ → Bool) (hEN : E < N)
    (hpE : p E = true) (hpost : ∀ i, E < i → i < N → p i = false) :
    ((List.range N).filter p).reverse.head?.getD 0 = E := by
  obtain ⟨d, hN⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hEN)
  have hr : List.range N = List.range E ++ [E] ++ (List.range d).map (fun t => E + 1 + t) := by
    rw [hN, List.range_add, List.range_succ]
  rw [hr, List.filter_append, List.filter_append]
  have hnil : ((List.range d).map (fun t => E + 1 + t)).filter p = [] :=
    List.filter_eq_nil_iff.mpr fun i hi => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hi
      rw [List.mem_range] at ht
      simpa using hpost (E + 1 + t) (by omega) (by omega)
  have hmid : [E].filter p = [E] := by simp [hpE]
  rw [hnil, hmid, List.append_nil, List.reverse_append]
  rfl

lemma binEndAfter_eq (pre : List Bool) (m : ℕ) (suf : List Bool)
    (heven : ∃ s, pre.length = 2 * s) :
    binEndAfter (pre ++ encBin m ++ suf) pre.length = pre.length + 2 * m.bits.length := by
  rcases heven with ⟨s, hs⟩; unfold binEndAfter
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
          rw [hs] at *; have hadd := congrArg Nat.bodd hieq
          rw [Nat.bodd_add, hbe, Bool.false_xor] at hadd; rw [← hadd]; simpa using hb
        have heq_two : i - pre.length = 2 * ((i - pre.length) / 2) := by
          have hmod : (i - pre.length) % 2 = 0 := by rw [Nat.mod_two_of_bodd, hbi]; rfl
          omega
        have hj : (i - pre.length) / 2 < m.bits.length := by omega
        have hget : (pre ++ encBin m ++ suf)[i]? = some true := by
          rw [List.append_assoc, List.getElem?_append_right (by omega),
            List.getElem?_append_left hsub_len, heq_two]
          exact encBin_getElem?_even hj
        rw [hget]; simp
  · have hsub_len : 2 * m.bits.length < (encBin m).length := by rw [encBin_length]; omega
    have hb : Nat.bodd (pre.length + 2 * m.bits.length) = false := by rw [hs, ← Nat.mul_add, Nat.bodd_mul]; simp
    have hget : (pre ++ encBin m ++ suf)[pre.length + 2 * m.bits.length]? = some false := by
      rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_append_left hsub_len]
      exact encBin_getElem?_end m
    rw [hget]; simp [hb]

lemma filter_range_odd_between (N s k : ℕ) (hN : 2 * s + 2 * k ≤ N) :
    (List.range N).filter (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * k) && Nat.bodd i) =
      (List.range k).map (fun j => 2 * s + 2 * j + 1) := by
  induction k with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, List.range_zero, List.map_nil]
    apply List.filter_eq_nil_iff.mpr; intro i _; simp
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
          (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * k) && Nat.bodd i) :=
        List.filter_congr fun i hi => by rw [List.mem_range] at hi; simp [hi, show i < 2 * s + 2 * (k + 1) by omega]
      have hnil_right0 : ((List.range d).map (fun t => 2 * s + 2 * k + 2 + t)).filter
          (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * k) && Nat.bodd i) = [] :=
        List.filter_eq_nil_iff.mpr fun i hi => by obtain ⟨t, _, rfl⟩ := List.mem_map.mp hi; simp; omega
      have hnil_right1 : ((List.range d).map (fun t => 2 * s + 2 * k + 2 + t)).filter
          (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * (k + 1)) && Nat.bodd i) = [] :=
        List.filter_eq_nil_iff.mpr fun i hi => by obtain ⟨t, _, rfl⟩ := List.mem_map.mp hi; simp; omega
      have hmid0 : [2 * s + 2 * k, 2 * s + 2 * k + 1].filter
          (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * k) && Nat.bodd i) = [] := by
        simp [show ¬ (2 * s + 2 * k + 1 < 2 * s + 2 * k) by omega]
      have hb_even : Nat.bodd (2 * s + 2 * k) = false := by rw [← Nat.mul_add, Nat.bodd_mul]; simp
      have hb_odd : Nat.bodd (2 * s + 2 * k + 1) = true := by rw [Nat.bodd_add, hb_even]; decide
      have hmid1 : [2 * s + 2 * k, 2 * s + 2 * k + 1].filter
          (fun i => decide (2 * s ≤ i) && decide (i < 2 * s + 2 * (k + 1)) && Nat.bodd i) =
          [2 * s + 2 * k + 1] := by
        simp [hb_even, show 2 * s ≤ 2 * s + 2 * k + 1 by omega, show 2 * s + 2 * k + 1 < 2 * s + 2 * (k + 1) by omega]
      simp only [List.filter_append, hnil_left1, hmid0, hmid1, hnil_right0, hnil_right1, List.append_nil]
    rw [hr, ih (by omega), List.range_succ, List.map_append]; rfl

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
      have hget : (pre ++ encBin m ++ suf)[2 * s + 2 * j + 1]? = some m.bits[j] := by
        rw [List.append_assoc, List.getElem?_append_right (by omega),
          show 2 * s + 2 * j + 1 - pre.length = 2 * j + 1 by omega,
          List.getElem?_append_left (by rw [encBin_length]; omega)]
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
    List.filter_eq_nil_iff.mpr fun i hi => by obtain ⟨t, _, rfl⟩ := List.mem_map.mp hi; simp
  rw [h1, h2, List.append_nil]

def pRaw (xs : List Bool) : ℕ := parseBinFrom xs 0
def pEndRaw (xs : List Bool) : ℕ := binEndAfter xs 0
def rRaw (xs : List Bool) : ℕ := parseBinFrom xs (pEndRaw xs + 2)
def qRaw (xs : List Bool) : ℕ :=
  prodList (((List.range xs.length).filter (fun i => decide (i < rRaw xs))).map (fun _ => pRaw xs))

@[fun_prop] lemma poly_pRaw : Automatic.Poly pRaw := by unfold pRaw; fun_prop
@[fun_prop] lemma poly_pEndRaw : Automatic.Poly pEndRaw := by unfold pEndRaw; fun_prop
@[fun_prop] lemma poly_rRaw : Automatic.Poly rRaw := by unfold rRaw; fun_prop
@[fun_prop] lemma poly_qRaw : Automatic.Poly qRaw := by unfold qRaw; fun_prop

lemma flatMap_encBin_length_ge (l : List ℕ) (f : ℕ → ℕ) :
    2 * l.length ≤ (l.flatMap (fun j => encBin (f j))).length := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, encBin_length]; omega

lemma encData_eq_encBin_p_r (D : FieldData) :
    ∃ suf : List Bool, D.encData = encBin D.p ++ encBin D.r ++ suf := by
  unfold FieldData.encData; simp only [List.append_assoc]; exact ⟨_, rfl⟩

lemma encData_length_ge_r (D : FieldData) : D.r ≤ D.encData.length := by
  unfold FieldData.encData
  have h2 := flatMap_encBin_length_ge (List.range (D.r + 1)) (fun j => (D.f.coeff j).val)
  simp only [List.length_append, List.length_range] at *; omega

lemma encData_ends_false (D : FieldData) : ∃ pref : List Bool, D.encData = pref ++ [false] := by
  have hbin : ∀ m : ℕ, ∃ pre, encBin m = pre ++ [false] := fun m =>
    ⟨(m.bits.flatMap (fun β => [true, β])) ++ [false], by simp [encBin, List.append_assoc]⟩
  have hflat : ∀ k : ℕ, 0 < k → ∀ g : ℕ → List Bool, (∀ i, ∃ pre, g i = pre ++ [false]) →
      ∃ pre, (List.range k).flatMap g = pre ++ [false] := by
    intro k hk g hg
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨pre, hpre⟩ := hg k'
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, hpre]
    simp only [← List.append_assoc]; exact ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ := hflat 2 (by omega) (fun j => (List.range D.r).flatMap fun l =>
    encBin (D.digit ((AdjoinRoot.modByMonicHom D.F_monic D.h).coeff j) l))
    (fun j => hflat D.r D.hr _ (fun l => hbin _))
  unfold FieldData.encData
  rw [hp1]
  simp only [← List.append_assoc]; exact ⟨_, rfl⟩

lemma qRaw_encData (D : FieldData) (b : ℕ) : qRaw (D.encData ++ encNat b) = D.q := by
  obtain ⟨suf, hsuf⟩ := encData_eq_encBin_p_r D
  have hp : pRaw (D.encData ++ encNat b) = D.p := by
    unfold pRaw
    have h : D.encData ++ encNat b = [] ++ encBin D.p ++ (encBin D.r ++ suf ++ encNat b) := by
      rw [hsuf]; simp [List.append_assoc]
    rw [h]; exact parseBinFrom_eq [] D.p (encBin D.r ++ suf ++ encNat b) ⟨0, rfl⟩
  have hpe : pEndRaw (D.encData ++ encNat b) = 2 * D.p.bits.length := by
    unfold pEndRaw
    have h : D.encData ++ encNat b = [] ++ encBin D.p ++ (encBin D.r ++ suf ++ encNat b) := by
      rw [hsuf]; simp [List.append_assoc]
    rw [h]; simpa using binEndAfter_eq [] D.p (encBin D.r ++ suf ++ encNat b) ⟨0, rfl⟩
  have hr : rRaw (D.encData ++ encNat b) = D.r := by
    unfold rRaw; rw [hpe]
    have hpre : (encBin D.p).length = 2 * D.p.bits.length + 2 := encBin_length D.p
    have h : D.encData ++ encNat b = encBin D.p ++ encBin D.r ++ (suf ++ encNat b) := by
      rw [hsuf]; simp [List.append_assoc]
    rw [h, ← hpre]
    exact parseBinFrom_eq (encBin D.p) D.r (suf ++ encNat b) ⟨D.p.bits.length + 1, by rw [hpre]; omega⟩
  unfold qRaw; rw [hr, hp, filter_range_lt_eq ((encData_length_ge_r D).trans (by simp))]
  have hrep : (List.range D.r).map (fun _ => D.p) = List.replicate D.r D.p := by
    apply List.ext_getElem <;> simp
  rw [hrep, prodList_replicate]; rfl

def dEndRaw (xs : List Bool) : ℕ :=
  ((List.range xs.length).filter (fun i => decide (i + 1 < xs.length) && !xs[i]?.getD false)).reverse.head?.getD 0

def bRaw (xs : List Bool) : ℕ := xs.length - 2 - dEndRaw xs

@[fun_prop] lemma poly_dEndRaw : Automatic.Poly dEndRaw := by unfold dEndRaw; fun_prop
@[fun_prop] lemma poly_bRaw : Automatic.Poly bRaw := by unfold bRaw; fun_prop

lemma bRaw_encData (D : FieldData) (b : ℕ) : bRaw (D.encData ++ encNat b) = b := by
  obtain ⟨pref, hpref⟩ := encData_ends_false D
  have hde : D.encData.length = pref.length + 1 := by rw [hpref]; simp
  have hend : dEndRaw (D.encData ++ encNat b) = pref.length := by
    unfold dEndRaw
    have hlen : (D.encData ++ encNat b).length = pref.length + b + 2 := by
      rw [List.length_append, hde]; simp [encNat]; omega
    rw [hlen]
    refine last?_filter_range _ (by omega) ?_ ?_
    · have hget : (D.encData ++ encNat b)[pref.length]? = some false := by
        rw [hpref, List.append_assoc, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
      rw [hget]
      simp [show pref.length + 1 < pref.length + b + 2 by omega]
    · intro i hi1 hi2
      by_cases hi_last : i + 1 < pref.length + b + 2
      · have hget : (D.encData ++ encNat b)[i]? = some true := by
          have hlt : i - D.encData.length < b := by omega
          rw [List.getElem?_append_right (by omega)]
          change (List.replicate b true ++ [false])[i - D.encData.length]? = some true
          rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate, if_pos hlt]
        rw [hget]; simp [hi_last]
      · simp [hi_last]
  unfold bRaw; rw [hend, hpref]; simp [encNat]; omega

def pow4ListAux (bs : List Bool) : ℕ := bs.foldl (fun acc _ => 4 * acc) 1

lemma poly_pow4ListAux : Automatic.Poly pow4ListAux := by
  have hop : Automatic.Poly (fun p : ℕ × Bool => 4 * p.1) := by fun_prop
  have hfold : Automatic.Poly (fun x : List Bool × ℕ => x.1.foldl (fun acc _ => 4 * acc) x.2) := by
    rcases hop with ⟨Pop⟩
    refine ⟨PolyProgram.listFoldLinear Pop false 2 fun acc a => ?_⟩
    have hle : (4 * acc).bits.length ≤ acc.bits.length + 2 := by
      rw [natBits_length_le_iff, Nat.pow_add]
      have h := natBits_length_le_iff.mp (le_refl acc.bits.length)
      nlinarith
    exact hle.trans (by change _ ≤ acc.bits.length + 2 * (2 * (encodeBool a).length + 1); omega)
  have hid : Automatic.Poly (fun bs : List Bool => bs) := by fun_prop
  have h1 : Automatic.Poly (fun _ : List Bool => (1 : ℕ)) := by fun_prop
  rcases hid with ⟨Pid⟩; rcases h1 with ⟨P1⟩; rcases hfold with ⟨Pf⟩
  exact ⟨((Pid.fanout P1).comp Pf).congr _ (fun _ => rfl)⟩

@[fun_prop] lemma poly_pow4ListAux_comp {α : Type} [Automatic.Coding α] {bs : α → List Bool}
    (hbs : Automatic.Poly bs) : Automatic.Poly (fun x => pow4ListAux (bs x)) := by
  rcases hbs with ⟨Pbs⟩; rcases poly_pow4ListAux with ⟨Pp⟩
  exact ⟨(Pbs.comp Pp).congr _ (fun _ => rfl)⟩

def pow4Raw (xs : List Bool) : ℕ :=
  pow4ListAux (((List.range xs.length).filter (fun i => decide (i < bRaw xs))).map (fun _ => false))

@[fun_prop] lemma poly_pow4Raw : Automatic.Poly pow4Raw := by unfold pow4Raw; fun_prop

lemma pow4ListAux_eq (bs : List Bool) : pow4ListAux bs = 4 ^ bs.length := by
  unfold pow4ListAux
  have h : ∀ acc, bs.foldl (fun a _ => 4 * a) acc = acc * 4 ^ bs.length := by
    intro acc; induction bs generalizing acc with
    | nil => simp
    | cons _ _ ih => simp only [List.foldl_cons, List.length_cons, pow_succ', ih]; ring
  simpa using h 1

lemma pow4Raw_encData (D : FieldData) (b : ℕ) : pow4Raw (D.encData ++ encNat b) = 4 ^ b := by
  unfold pow4Raw; rw [bRaw_encData]
  have hle : b ≤ (D.encData ++ encNat b).length := by simp [encNat]; omega
  rw [filter_range_lt_eq hle, pow4ListAux_eq, List.length_map, List.length_range]

def pow2Bits (n : ℕ) : ℕ := n.bits.foldl (fun acc _ => 2 * acc) 1

lemma poly_pow2Bits : Automatic.Poly pow2Bits := by
  have hop : Automatic.Poly (fun p : ℕ × Bool => 2 * p.1) := by fun_prop
  have hfold : Automatic.Poly (fun x : List Bool × ℕ => x.1.foldl (fun acc _ => 2 * acc) x.2) := by
    rcases hop with ⟨Pop⟩
    refine ⟨PolyProgram.listFoldLinear Pop false 1 fun acc a => ?_⟩
    have hle : (2 * acc).bits.length ≤ acc.bits.length + 1 := by
      rw [natBits_length_le_iff, Nat.pow_succ']
      have h := natBits_length_le_iff.mp (le_refl acc.bits.length)
      omega
    exact hle.trans (by change _ ≤ acc.bits.length + 1 * (2 * (encodeBool a).length + 1); omega)
  have hbits : Automatic.Poly Nat.bits := poly_natBits
  have h1 : Automatic.Poly (fun _ : ℕ => (1 : ℕ)) := by fun_prop
  rcases hbits with ⟨Pb⟩; rcases h1 with ⟨P1⟩; rcases hfold with ⟨Pf⟩
  exact ⟨((Pb.fanout P1).comp Pf).congr _ (fun _ => rfl)⟩

lemma pow2Bits_eq (n : ℕ) : pow2Bits n = 2 ^ n.bits.length := by
  unfold pow2Bits
  have h : ∀ bs : List Bool, ∀ acc, bs.foldl (fun a _ => 2 * a) acc = acc * 2 ^ bs.length := by
    intro bs acc; induction bs generalizing acc with
    | nil => simp
    | cons _ _ ih => simp only [List.foldl_cons, List.length_cons, pow_succ', ih]; ring
  simpa using h n.bits 1

def sqrtStep (st : ℕ × ℕ × ℕ) (_ : Bool) : ℕ × ℕ × ℕ :=
  let p' := st.2.1 / 2
  let cand := st.2.2 + p'
  if cand * cand ≤ st.1 then (st.1, p', cand) else (st.1, p', st.2.2)

@[fun_prop] lemma poly_sqrtStep :
    Automatic.Poly (fun x : (ℕ × ℕ × ℕ) × Bool => sqrtStep x.1 x.2) := by
  unfold sqrtStep; fun_prop

lemma sqrtStep_fold_le (bs : List Bool) (n p acc : ℕ) :
    (bs.foldl sqrtStep (n, p, acc)).1 = n ∧
    (bs.foldl sqrtStep (n, p, acc)).2.1 ≤ p ∧
    (bs.foldl sqrtStep (n, p, acc)).2.2 ≤ acc + p := by
  induction bs generalizing p acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, sqrtStep]
    split_ifs with hcond
    · obtain ⟨h1, h2, h3⟩ := ih (p / 2) (acc + p / 2)
      refine ⟨h1, h2.trans (Nat.div_le_self _ _), h3.trans (by omega)⟩
    · obtain ⟨h1, h2, h3⟩ := ih (p / 2) acc
      refine ⟨h1, h2.trans (Nat.div_le_self _ _), h3.trans (by omega)⟩

def sqrtNat (n : ℕ) : ℕ := (n.bits.foldl sqrtStep (n, pow2Bits n, 0)).2.2

@[fun_prop] lemma poly_sqrtNat : Automatic.Poly sqrtNat := by
  have hfold : Automatic.Poly (fun x : List Bool × (ℕ × ℕ × ℕ) => x.1.foldl sqrtStep x.2) := by
    rcases poly_sqrtStep with ⟨Ps⟩
    refine ⟨PolyProgram.listFold Ps false (2 * Polynomial.X) ?_⟩
    intro as st pre suf _
    rcases st with ⟨n, p, acc⟩
    obtain ⟨h1, h2, h3⟩ := sqrtStep_fold_le pre n p acc
    have hb1 : (pre.foldl sqrtStep (n, p, acc)).1.bits.length = n.bits.length := by rw [h1]
    have hb2 : (pre.foldl sqrtStep (n, p, acc)).2.1.bits.length ≤ p.bits.length := bits_length_mono h2
    have hb3 : (pre.foldl sqrtStep (n, p, acc)).2.2.bits.length ≤ (acc + p).bits.length := bits_length_mono h3
    change (encodePair Nat.bits (encodePair Nat.bits Nat.bits) (pre.foldl sqrtStep (n, p, acc))).length ≤
      (2 * Polynomial.X).eval
        (encodePair (encodeList encodeBool) (encodePair Nat.bits (encodePair Nat.bits Nat.bits)) (as, (n, p, acc))).length
    simp only [encodePair_length, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    have hsum : (acc + p).bits.length ≤ acc.bits.length + p.bits.length + 1 := by
      rw [natBits_length_le_iff]
      have hacc := natBits_length_le_iff.mp (le_refl acc.bits.length)
      have hp := natBits_length_le_iff.mp (le_refl p.bits.length)
      have hpow : 2 ^ acc.bits.length + 2 ^ p.bits.length ≤ 2 ^ (acc.bits.length + p.bits.length + 1) := by
        have h1 : 2 ^ acc.bits.length ≤ 2 ^ (acc.bits.length + p.bits.length) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have h2 : 2 ^ p.bits.length ≤ 2 ^ (acc.bits.length + p.bits.length) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.pow_succ]; omega
      omega
    omega
  rcases poly_natBits with ⟨Pbits⟩
  rcases poly_pow2Bits with ⟨Pp2⟩
  rcases (by fun_prop : Automatic.Poly (fun n : ℕ => n)) with ⟨Pid⟩
  rcases (by fun_prop : Automatic.Poly (fun _ : ℕ => (0 : ℕ))) with ⟨P0⟩
  rcases (by fun_prop : Automatic.Poly (fun st : ℕ × ℕ × ℕ => st.2.2)) with ⟨Pout⟩
  rcases hfold with ⟨Pf⟩
  have Pinit : PolyProgram Nat.bits (encodePair Nat.bits (encodePair Nat.bits Nat.bits))
      (fun n => (n, pow2Bits n, 0)) := Pid.fanout (Pp2.fanout P0)
  exact ⟨((Pbits.fanout Pinit).comp Pf |>.comp Pout).congr _ (fun _ => rfl)⟩

@[fun_prop] lemma poly_sqrtNat_comp {α : Type} [Automatic.Coding α] {f : α → ℕ}
    (hf : Automatic.Poly f) : Automatic.Poly (fun x => sqrtNat (f x)) := by
  rcases hf with ⟨Pf⟩; rcases poly_sqrtNat with ⟨Ps⟩; exact ⟨(Pf.comp Ps).congr _ (fun _ => rfl)⟩

lemma sqrt_fold_spec (bs : List Bool) (n p acc : ℕ) (hp : p = 2 ^ bs.length)
    (hlo : acc ^ 2 ≤ n) (hhi : n < (acc + p) ^ 2) :
    let st := bs.foldl sqrtStep (n, p, acc)
    st.2.2 ^ 2 ≤ n ∧ n < (st.2.2 + 1) ^ 2 := by
  induction bs generalizing p acc with
  | nil =>
    simp only [List.length_nil, pow_zero] at hp
    simpa [hp] using And.intro hlo hhi
  | cons _ tl ih =>
    simp only [List.length_cons, pow_succ'] at hp
    have hdiv : p / 2 = 2 ^ tl.length := by rw [hp, Nat.mul_div_right _ (by decide)]
    simp only [List.foldl_cons, sqrtStep]
    split_ifs with hcond
    · apply ih (p / 2) (acc + p / 2) hdiv (by simpa [sq] using hcond)
      simpa [show acc + p / 2 + p / 2 = acc + p by omega] using hhi
    · apply ih (p / 2) acc hdiv hlo
      have hgt : n < (acc + p / 2) * (acc + p / 2) := Nat.lt_of_not_le hcond
      simpa [sq] using hgt

lemma sqrtNat_eq (n : ℕ) : sqrtNat n = Nat.sqrt n := by
  unfold sqrtNat
  rw [pow2Bits_eq]
  have hspec := sqrt_fold_spec n.bits n (2 ^ n.bits.length) 0 rfl (by simp) (by
    have hn : n < 2 ^ n.bits.length := natBits_length_le_iff.mp le_rfl
    have hle : 2 ^ n.bits.length ≤ (0 + 2 ^ n.bits.length) ^ 2 := by
      simpa using Nat.le_self_pow (by decide : 2 ≠ 0) (2 ^ n.bits.length)
    omega)
  exact le_antisymm (Nat.le_sqrt.mpr (by simpa [sq] using hspec.1))
    (Nat.lt_succ_iff.mp (Nat.sqrt_lt'.mpr (by simpa [sq] using hspec.2)))

def encNatBin (m : ℕ) : List Bool := m.bits.flatMap (fun β => [true, β]) ++ [false, false]
def encPosInt (m : ℕ) : List Bool := [false] ++ encNatBin m
def encNegInt (m : ℕ) : List Bool := if m = 0 then [false] ++ encNatBin 0 else [true] ++ encNatBin m

@[fun_prop] lemma poly_encNatBin : Automatic.Poly encNatBin := by unfold encNatBin; fun_prop
@[fun_prop] lemma poly_encPosInt : Automatic.Poly encPosInt := by unfold encPosInt; fun_prop
@[fun_prop] lemma poly_encNegInt : Automatic.Poly encNegInt := by unfold encNegInt; fun_prop

def u2ApproxQBuilder (xs : List Bool) : Str :=
  let q := qRaw xs
  let p4 := pow4Raw xs
  let c0 := sqrtNat ((q * p4) / (q + 1))
  let s0 := sqrtNat (p4 / (q + 1))
  encPosInt c0 ++ encPosInt 0 ++ encNegInt s0 ++ encPosInt 0 ++
    encPosInt s0 ++ encPosInt 0 ++ encPosInt c0 ++ encPosInt 0

lemma poly_u2ApproxQBuilder : Automatic.Poly u2ApproxQBuilder := by
  unfold u2ApproxQBuilder; fun_prop

lemma encNegInt_eq (m : ℕ) : encNegInt m = encSignedNat (-(m : ℤ)) := by
  unfold encNegInt encSignedNat encNatBin encBin
  cases m with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    have hneg : (-(↑(m + 1) : ℤ) < 0) := by omega
    have hnat : (-(↑(m + 1) : ℤ)).natAbs = m + 1 := by omega
    rw [if_pos hneg, hnat]

lemma encPosInt_eq (m : ℕ) : encPosInt m = encSignedNat (m : ℤ) := by
  unfold encPosInt encSignedNat encNatBin encBin
  have hnn : ¬ ((m : ℤ) < 0) := by omega
  simp [hnn]

def U_q (D : FieldData) : Matrix (Qubits 1) (Qubits 1) ℂ :=
  Matrix.of fun i j =>
    match i 0, j 0 with
    | false, false => (Real.sqrt ((D.q : ℝ) / ((D.q : ℝ) + 1)) : ℂ)
    | false, true  => -(Real.sqrt (1 / ((D.q : ℝ) + 1)) : ℂ)
    | true,  false => (Real.sqrt (1 / ((D.q : ℝ) + 1)) : ℂ)
    | true,  true  => (Real.sqrt ((D.q : ℝ) / ((D.q : ℝ) + 1)) : ℂ)

lemma sum_qubits1 {M : Type*} [AddCommMonoid M] (f : Qubits 1 → M) :
    (∑ x : Qubits 1, f x) = f (fun _ => false) + f (fun _ => true) := by
  let e : Qubits 1 ≃ Bool := ⟨fun q => q 0, fun b _ => b,
    fun q => funext fun i => by fin_cases i; rfl, fun b => rfl⟩
  rw [Fintype.sum_equiv e f (fun b => f (e.symm b)) (fun q => congrArg f (e.symm_apply_apply q).symm),
    Fintype.sum_bool, add_comm]
  rfl

lemma U_q_unitary (D : FieldData) : U_q D ∈ Matrix.unitaryGroup (Qubits 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, sum_qubits1, RCLike.star_def]
  have hq0 : (0 : ℝ) < D.q := by exact_mod_cast (by have := D.one_lt_q; omega : 0 < D.q)
  have hc2 : Real.sqrt ((D.q : ℝ) / ((D.q : ℝ) + 1)) * Real.sqrt ((D.q : ℝ) / ((D.q : ℝ) + 1)) =
      (D.q : ℝ) / ((D.q : ℝ) + 1) := Real.mul_self_sqrt (by positivity)
  have hs2 : Real.sqrt (1 / ((D.q : ℝ) + 1)) * Real.sqrt (1 / ((D.q : ℝ) + 1)) =
      1 / ((D.q : ℝ) + 1) := Real.mul_self_sqrt (by positivity)
  have hcs_r : ((D.q : ℝ) / ((D.q : ℝ) + 1)) + (1 / ((D.q : ℝ) + 1)) = 1 := by
    field_simp
  have hcs : ((Real.sqrt ((D.q : ℝ) / ((D.q : ℝ) + 1)) : ℂ) * (Real.sqrt ((D.q : ℝ) / ((D.q : ℝ) + 1)) : ℂ)) +
      ((Real.sqrt (1 / ((D.q : ℝ) + 1)) : ℂ) * (Real.sqrt (1 / ((D.q : ℝ) + 1)) : ℂ)) = 1 := by
    have hr : Real.sqrt ((D.q : ℝ) / ((D.q : ℝ) + 1)) * Real.sqrt ((D.q : ℝ) / ((D.q : ℝ) + 1)) +
        Real.sqrt (1 / ((D.q : ℝ) + 1)) * Real.sqrt (1 / ((D.q : ℝ) + 1)) = 1 := by
      rw [hc2, hs2, hcs_r]
    exact_mod_cast hr
  by_cases hij : i = j
  · subst hij
    cases hi : i 0 <;> simp only [U_q, Matrix.of_apply, hi, Complex.conj_ofReal, map_neg,
        mul_neg, neg_mul, neg_neg] <;>
      [exact hcs; (rw [add_comm]; exact hcs)]
  · have h0ne : i 0 ≠ j 0 := fun heq => hij (funext fun k => by fin_cases k; exact heq)
    rw [if_neg hij]
    cases hi : i 0 <;> cases hj : j 0 <;> simp_all [U_q, Complex.conj_ofReal] <;> ring

lemma sqrt_div_dyadic_err (c d b : ℕ) (hd : 0 < d) :
    let s := Nat.sqrt ((c * 4 ^ b) / d)
    |Real.sqrt ((c : ℝ) / (d : ℝ)) - (s : ℝ) / (2 : ℝ) ^ b| ≤ (1 / 2 : ℝ) ^ b := by
  intro s
  have hd_r : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h2b : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have h4b : (4 : ℝ) ^ b = ((2 : ℝ) ^ b) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm 2 b]
  set k : ℕ := (c * 4 ^ b) / d
  have hk_lo : (s : ℝ) ^ 2 ≤ ((c : ℝ) * (4 : ℝ) ^ b) / (d : ℝ) := by
    have h1 : s ^ 2 ≤ k := by simpa [sq] using Nat.sqrt_le (c * 4 ^ b / d)
    have h2 : (k : ℝ) ≤ ((c : ℝ) * (4 : ℝ) ^ b) / (d : ℝ) := by
      rw [le_div_iff₀ hd_r]
      exact_mod_cast Nat.div_mul_le_self (c * 4 ^ b) d
    exact (by exact_mod_cast h1 : (s : ℝ) ^ 2 ≤ k).trans h2
  have hk_hi : ((c : ℝ) * (4 : ℝ) ^ b) / (d : ℝ) < ((s + 1 : ℝ)) ^ 2 := by
    have h1 : k + 1 ≤ (s + 1) ^ 2 := by
      simpa [sq, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt (c * 4 ^ b / d)
    have h2 : ((c : ℝ) * (4 : ℝ) ^ b) / (d : ℝ) < (k : ℝ) + 1 := by
      rw [div_lt_iff₀ hd_r]
      have hmod : c * 4 ^ b < (k + 1) * d := by
        have := Nat.lt_div_mul_add (a := c * 4 ^ b) hd
        change c * 4 ^ b < k * d + d at this
        linarith
      exact_mod_cast hmod
    exact h2.trans_le (by exact_mod_cast h1)
  have hsq_r : (Real.sqrt ((c : ℝ) / (d : ℝ)) * (2 : ℝ) ^ b) ^ 2 =
      ((c : ℝ) * (4 : ℝ) ^ b) / (d : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← h4b]; ring
  have hprod_lo : (s : ℝ) ≤ Real.sqrt ((c : ℝ) / (d : ℝ)) * (2 : ℝ) ^ b := by
    rw [← sq_le_sq₀ (Nat.cast_nonneg s) (by positivity), hsq_r]; exact hk_lo
  have hprod_hi : Real.sqrt ((c : ℝ) / (d : ℝ)) * (2 : ℝ) ^ b < (s : ℝ) + 1 := by
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) (by rw [hsq_r]; exact hk_hi)
  have hdiff : |Real.sqrt ((c : ℝ) / (d : ℝ)) * (2 : ℝ) ^ b - (s : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc |Real.sqrt ((c : ℝ) / (d : ℝ)) - (s : ℝ) / (2 : ℝ) ^ b|
      = |(Real.sqrt ((c : ℝ) / (d : ℝ)) * (2 : ℝ) ^ b - (s : ℝ)) / (2 : ℝ) ^ b| := by
          congr 1; field_simp
    _ = |Real.sqrt ((c : ℝ) / (d : ℝ)) * (2 : ℝ) ^ b - (s : ℝ)| / (2 : ℝ) ^ b := by
          rw [abs_div, abs_of_pos h2b]
    _ ≤ 1 / (2 : ℝ) ^ b := by exact div_le_div_of_nonneg_right hdiff h2b.le
    _ = (1 / 2 : ℝ) ^ b := by simp [one_div, inv_pow]

lemma U_q_approx : IsPolyApproxU2 (fun _ => True) U_q := by
  refine ⟨u2ApproxQBuilder, ?_, ?_⟩
  · rcases poly_u2ApproxQBuilder with ⟨P⟩
    exact ⟨((BooleanLists.packProgram.comp P).comp BooleanLists.unpackProgram).stock⟩
  · intro D _ b
    set c0 : ℕ := Nat.sqrt ((D.q * 4 ^ b) / (D.q + 1))
    set s0 : ℕ := Nat.sqrt (4 ^ b / (D.q + 1))
    let a : Qubits 1 → Qubits 1 → ℤ × ℤ := fun i j =>
      match i 0, j 0 with
      | false, false => (c0, 0)
      | false, true  => (-s0, 0)
      | true,  false => (s0, 0)
      | true,  true  => (c0, 0)
    refine ⟨a, ?_, ?_⟩
    · unfold u2ApproxQBuilder
      dsimp only
      rw [qRaw_encData, pow4Raw_encData, sqrtNat_eq, sqrtNat_eq]
      simp only [encU2Approx, encDyadicC, encPosInt_eq, encNegInt_eq, a, List.append_assoc]
      rfl
    · intro i j
      have hc := sqrt_div_dyadic_err D.q (D.q + 1) b (by omega)
      have hs := sqrt_div_dyadic_err 1 (D.q + 1) b (by omega)
      have hdyad_pos : ∀ m : ℕ, (dyadicC b ((m : ℤ), (0 : ℤ))) = (((m : ℝ) / (2 : ℝ) ^ b : ℝ) : ℂ) := by
        intro m; simp [dyadicC]
      have hdyad_neg : ∀ m : ℕ, (dyadicC b (-(m : ℤ), (0 : ℤ))) = (-((m : ℝ) / (2 : ℝ) ^ b : ℝ) : ℂ) := by
        intro m; simp [dyadicC, neg_div]
      cases hi : i 0 <;> cases hj : j 0
      · simp only [U_q, Matrix.of_apply, a, hi, hj, hdyad_pos]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        simpa [Nat.cast_add, Nat.cast_one] using hc
      · simp only [U_q, Matrix.of_apply, a, hi, hj, hdyad_neg, sub_neg_eq_add]
        rw [show -(Real.sqrt (1 / ((D.q : ℝ) + 1)) : ℂ) + (((s0 : ℝ) / (2 : ℝ) ^ b : ℝ) : ℂ) =
            -(((Real.sqrt ((1 : ℕ) / ((D.q + 1 : ℕ) : ℝ)) - (s0 : ℝ) / (2 : ℝ) ^ b) : ℝ) : ℂ) by
              push_cast; ring]
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]; simpa using hs
      · simp only [U_q, Matrix.of_apply, a, hi, hj, hdyad_pos]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; simpa using hs
      · simp only [U_q, Matrix.of_apply, a, hi, hj, hdyad_pos]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        simpa [Nat.cast_add, Nat.cast_one] using hc

/-! ### Section 3: Exact `D.q = 2` field, representation, and `A70` lemmas -/

lemma q_eq_two_p_r (D : FieldData) (hq2 : D.q = 2) :
    D.p = 2 ∧ D.r = 1 ∧ D.labW = 2 := by
  have hpr : D.p ^ D.r = 2 := by simpa [FieldData.q] using hq2
  have hp2 : 2 ≤ D.p := D.hp.two_le
  have hr1 : 1 ≤ D.r := D.hr
  have hr_eq : D.r = 1 := by
    by_contra hne
    have hr2 : 2 ≤ D.r := by omega
    have hpow : 4 ≤ D.p ^ D.r :=
      (show 4 ≤ 2 ^ 2 by decide).trans ((Nat.pow_le_pow_right (by decide) hr2).trans
        (Nat.pow_le_pow_left hp2 D.r))
    omega
  rw [hr_eq, pow_one] at hpr
  refine ⟨hpr, hr_eq, ?_⟩
  rw [FieldData.labW, hq2]
  decide

lemma lab_eq_zero_of_q2 (D : FieldData) (hq2 : D.q = 2) (α : D.Lab) : α = 0 := by
  have : NeZero (D.q - 1) := ⟨by omega⟩
  have hlt : α.val < 1 := by
    have := ZMod.val_lt α
    omega
  exact (ZMod.val_eq_zero α).mp (by omega)

lemma isCusp_one_q2 (D : FieldData) (hq2 : D.q = 2) : D.IsCuspLabel (1 : D.Lab2) := by
  have : NeZero (D.q ^ 2 - 1) := ⟨by rw [hq2]; decide⟩
  have h3 : D.q ^ 2 - 1 = 3 := by rw [hq2]; norm_num
  have : Fact (1 < D.q ^ 2 - 1) := ⟨by omega⟩
  have h1val : (1 : D.Lab2).val = 1 := by simpa using ZMod.val_one (D.q ^ 2 - 1)
  have hq1 : ((D.q : D.Lab2) * 1).val = 2 := by
    rw [mul_one, ZMod.val_natCast, h3, hq2]
  refine ⟨?_, ?_⟩
  · rw [h1val, hq2]; decide
  · rw [h1val, hq1]; decide

def cusp1 (D : FieldData) (hq2 : D.q = 2) : {k : D.Lab2 // D.IsCuspLabel k} :=
  ⟨1, isCusp_one_q2 D hq2⟩

lemma cusp_eq_cusp1_q2 (D : FieldData) (hq2 : D.q = 2) (k : {k : D.Lab2 // D.IsCuspLabel k}) :
    k = cusp1 D hq2 := by
  apply Subtype.ext
  have : NeZero (D.q ^ 2 - 1) := ⟨by rw [hq2]; decide⟩
  have h3 : D.q ^ 2 - 1 = 3 := by rw [hq2]; norm_num
  have hlt : k.1.val < 3 := by have := ZMod.val_lt k.1; omega
  have hndiv : ¬ (3 ∣ k.1.val) := by simpa [hq2] using k.2.1
  have hmul : k.1.val ≤ ((D.q : D.Lab2) * k.1).val := k.2.2
  have hk0 : k.1.val ≠ 0 := fun hz => hndiv ⟨0, hz⟩
  have hk2 : k.1.val ≠ 2 := fun h2 => by
    have hv : ((D.q : D.Lab2) * k.1).val = 1 := by
      rw [ZMod.val_mul, h2, ZMod.val_natCast, h3, hq2]
    omega
  have hk1 : k.1.val = 1 := by omega
  have : k.1 = (k.1.val : D.Lab2) := (ZMod.natCast_zmod_val k.1).symm
  rw [this, hk1, Nat.cast_one]
  rfl

lemma chi_zero_neg_one (D : FieldData) : D.chi 0 (-1) = 1 := by
  have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  simp [FieldData.chi, hm1]

lemma chi_zero_one (D : FieldData) : D.chi 0 1 = 1 := by
  simp [FieldData.chi]

lemma fq_elems_q2 (D : FieldData) (hq2 : D.q = 2) (x : D.Fq) : x = 0 ∨ x = 1 := by
  have hcard : Fintype.card D.Fq = 2 := by
    have hfin : Module.finrank (ZMod D.p) D.Fq = D.r := by
      rw [(AdjoinRoot.powerBasis' D.f_monic).finrank, AdjoinRoot.powerBasis'_dim, D.f_deg]
    have hc := Module.card_eq_pow_finrank (K := ZMod D.p) (V := D.Fq)
    rw [ZMod.card, hfin] at hc
    rw [← FieldData.q, hq2] at hc
    exact hc
  have hx2 : x ^ 2 = x := by rw [← hcard]; exact FiniteField.pow_card x
  have hmul : x * (x - 1) = 0 := by linear_combination hx2
  rcases mul_eq_zero.mp hmul with rfl | hsub
  · exact Or.inl rfl
  · exact Or.inr (sub_eq_zero.mp hsub)

lemma psi_zero (D : FieldData) : D.psi 0 = 1 := by simp [FieldData.psi]

lemma psi_one_q2 (D : FieldData) (hq2 : D.q = 2) : D.psi 1 = -1 := by
  obtain ⟨hp2, hr1, _⟩ := q_eq_two_p_r D hq2
  have hfin : Module.finrank (ZMod D.p) D.Fq = 1 := by
    rw [(AdjoinRoot.powerBasis' D.f_monic).finrank, AdjoinRoot.powerBasis'_dim, D.f_deg, hr1]
  have htr : Algebra.trace (ZMod D.p) D.Fq 1 = 1 := by
    change LinearMap.trace (ZMod D.p) D.Fq (Algebra.lmul (ZMod D.p) D.Fq 1) = 1
    rw [map_one]
    change LinearMap.trace (ZMod D.p) D.Fq LinearMap.id = 1
    rw [LinearMap.trace_id, hfin, Nat.cast_one]
  unfold FieldData.psi
  rw [htr]
  have : Fact (1 < D.p) := ⟨by omega⟩
  have hval : (1 : ZMod D.p).val = 1 := ZMod.val_one D.p
  rw [hval, hp2]
  norm_num
  rw [show (2 : ℂ) * Real.pi * Complex.I / 2 = Real.pi * Complex.I by ring, Complex.exp_pi_mul_I]

lemma sum_fq_q2 {M : Type*} [AddCommMonoid M] (D : FieldData) (hq2 : D.q = 2) (f : D.Fq → M) :
    (∑ x : D.Fq, f x) = f 0 + f 1 := by
  have hne : (0 : D.Fq) ≠ 1 := zero_ne_one
  have huniv : (Finset.univ : Finset D.Fq) = {0, 1} := by
    ext x; simp [fq_elems_q2 D hq2 x]
  rw [huniv, Finset.sum_pair hne]

lemma sum_option_fq_q2 {M : Type*} [AddCommMonoid M] (D : FieldData) (hq2 : D.q = 2)
    (f : Option D.Fq → M) :
    (∑ x : Option D.Fq, f x) = f none + f (some 0) + f (some 1) := by
  rw [Fintype.sum_option, sum_fq_q2 D hq2]
  ring_nf
  abel

lemma wVec_0_q2 (D : FieldData) (hq2 : D.q = 2) (y : Option D.Fq) :
    D.wVec 0 0 y = D.vT 1 y := by
  unfold FieldData.wVec
  have hfilt : Finset.univ.filter (fun t : D.Fq => t ≠ 0) = ({1} : Finset D.Fq) := by
    ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rcases fq_elems_q2 D hq2 t with rfl | rfl
    · simp
    · simp [one_ne_zero]
  rw [hfilt, Finset.sum_singleton, neg_zero]
  simp only [chi_zero_one, mul_one, one_mul, hq2]
  simp [FieldData.isqrt]
  norm_num

lemma psModel_00_wGL_apply (D : FieldData) (y x : Option D.Fq) :
    D.psModel 0 0 ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) y x =
      match x with
      | none => if y = some 0 then 1 else 0
      | some x' =>
        if x' = 0 then (if y = none then 1 else 0)
        else if y = some x'⁻¹ then 1 else 0 := by
  have hw00 : ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 = 0 := rfl
  have hw01 : ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 1 := rfl
  have hw10 : ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 1 := rfl
  have hw11 : ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 = 0 := rfl
  dsimp only [FieldData.psModel]; rw [hw00, hw01, hw10, hw11]
  cases x with
  | none => dsimp only; simp [chi_zero_one]
  | some x' =>
    dsimp only; by_cases hx : x' = 0
    · subst hx; simp [chi_zero_one]
    · have hcond : (1 : D.Fq) * x' + 0 ≠ 0 := by simpa using hx
      have hloc : ((0 : D.Fq) * x' + 1) / ((1 : D.Fq) * x' + 0) = x'⁻¹ := by simp [one_div]
      have hdet : ((0 : D.Fq) * 0 - 1 * 1) / ((1 : D.Fq) * x' + 0) = -x'⁻¹ := by field_simp [hx]; ring
      rw [if_pos hcond, hloc, hdet]
      have hne1 : (-x'⁻¹ : D.Fq) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hx)
      split_ifs with hy
      · simp [FieldData.chi, hne1, hx]
      · rfl

lemma A70_off_q2_left (D : FieldData) (hq2 : D.q = 2) :
    A70 D (.inl (0, 0)) (.inr 0) (.inl (0, 0)) true (.inr (.inl 0)) = 1 := by
  rw [A70, if_pos rfl]
  let u0 : D.BBas (.inl (0, 0)) := PUnit.unit
  let b0 : D.BBas (.inr 0) := (0 : D.Lab)
  have ht : (tLab D) (.inr 0) (0, 0) = some b0 := by
    rw [tLab, if_pos (by ring)]
  rw [ht]
  have hB1 : Fintype.card (D.BBas (.inl (0, 0))) = 1 := Fintype.card_unit
  have hB2 : Fintype.card (D.BBas (.inr 0)) = 1 := by
    change Fintype.card D.Lab = 1; rw [ZMod.card]; omega
  have hbas : Fintype.card (D.Bas (.inr (.inl 0))) = 2 := by
    change Fintype.card (Option D.Lab) = 2; rw [Fintype.card_option, ZMod.card]; omega
  have hsum_unit : ∀ f : D.BBas (.inl (0, 0)) → ℂ, (∑ P : D.BBas (.inl (0, 0)), f P) = f u0 := fun f => by
    have hun : (Finset.univ : Finset (D.BBas (.inl (0, 0)))) = {u0} := by
      ext x; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; rfl
    rw [hun, Finset.sum_singleton]
  rw [hsum_unit]; dsimp only
  have hutw : (utwW D) (.inl (0, 0)) (0, 0) u0 = 1 := by simp [utwW]
  have hl1 : (labMu D) (.inr (.inl 0)) (.inr 0) b0 = some (some 0) := by
    simp [labMu, b0]; rfl
  have hl2 : (labMu D) (.inr (.inl 0)) (.inl (0, 0)) u0 = some none := by
    simp [labMu]; rfl
  rw [hutw, map_one, mul_one, hl1, hl2]
  unfold Rent
  rw [hbas, hB1, hB2]
  dsimp only [FieldData.R]
  simp only [Nat.cast_ofNat, Nat.cast_one]
  rw [show Real.sqrt (2 * (D.q : ℝ) / (1 * 1 * 1 * ((D.q : ℝ) + 1))) =
      Real.sqrt (2 * 2 / (1 * 1 * 1 * (2 + 1))) by rw [hq2]; norm_num]
  change (Real.sqrt (2 * 2 / (1 * 1 * 1 * (2 + 1))) : ℂ) *
      matEntry (D.psModel 0 0 ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq))
        (D.wVec 0 0) (D.stVec 0 none) = 1
  unfold matEntry
  simp_rw [wVec_0_q2 D hq2, sum_option_fq_q2 D hq2]
  have hnone : D.vT 1 none = 0 := rfl
  have hs0 : D.vT 1 (some 0) = FieldData.isqrt 2 := by simp [FieldData.vT, hq2, psi_zero]
  have hs1 : D.vT 1 (some 1) = -FieldData.isqrt 2 := by
    simp [FieldData.vT, hq2, psi_one_q2 D hq2]
  have hv_none : D.stVec 0 none none = FieldData.isqrt 3 * (Real.sqrt 2 : ℂ) := by
    simp only [FieldData.stVec, hq2, chi_zero_neg_one, Nat.cast_ofNat, mul_one]
    rw [show (2 : ℝ) + 1 = 3 by norm_num]
  have hv_0 : D.stVec 0 none (some 0) = -(FieldData.isqrt 3 * FieldData.isqrt 2) := by
    simp only [FieldData.stVec, hq2, Nat.cast_ofNat]
    rw [show (2 : ℝ) + 1 = 3 by norm_num]; ring
  have hv_1 : D.stVec 0 none (some 1) = -(FieldData.isqrt 3 * FieldData.isqrt 2) := by
    simp only [FieldData.stVec, hq2, Nat.cast_ofNat]
    rw [show (2 : ℝ) + 1 = 3 by norm_num]; ring
  have h01 : (0 : D.Fq) ≠ 1 := zero_ne_one
  have h10 : (1 : D.Fq) ≠ 0 := one_ne_zero
  simp only [hnone, hs0, hs1, map_zero, star_zero, zero_mul, zero_add,
    psModel_00_wGL_apply, hv_none, hv_0, hv_1, if_pos rfl, if_neg h01, if_neg h10,
    inv_one, Option.some.injEq, ↓reduceIte, mul_one, mul_zero, add_zero]
  have hring_real : ∀ r : ℝ, starRingEnd ℂ (r : ℂ) = (r : ℂ) := fun r => Complex.conj_ofReal r
  have hr : Real.sqrt (2 * 2 / (1 * (2 + 1))) *
      ((Real.sqrt 2)⁻¹ * ((Real.sqrt 3)⁻¹ * Real.sqrt 2) +
       (-(Real.sqrt 2)⁻¹ * -((Real.sqrt 3)⁻¹ * (Real.sqrt 2)⁻¹))) = 1 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have hnum : Real.sqrt (2 * 2 / (1 * (2 + 1))) = 2 * (Real.sqrt 3)⁻¹ := by
      rw [show (2 : ℝ) * 2 / (1 * (2 + 1)) = 4 / 3 by norm_num, Real.sqrt_div (by norm_num),
        show Real.sqrt 4 = 2 by norm_num, div_eq_mul_inv]
    rw [hnum]
    have hp1 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hp3 : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
    nlinarith [h2, h3]
  simp only [FieldData.isqrt, map_neg, hring_real]
  split_ifs
  all_goals first
    | contradiction
    | (simp only [mul_zero, zero_mul, add_zero, zero_add]; exact_mod_cast hr)

lemma A70_off_q2_right (D : FieldData) (hq2 : D.q = 2) :
    A70 D (.inr 0) (.inl (0, 0)) (.inl (0, 0)) true (.inr (.inl 0)) = 1 := by
  rw [A70, if_pos rfl]
  let u0 : D.BBas (.inl (0, 0)) := PUnit.unit
  let b0 : D.BBas (.inr 0) := (0 : D.Lab)
  have ht : (tLab D) (.inl (0, 0)) (0, 0) = some u0 := by simp [tLab, u0]
  rw [ht]
  have hB1 : Fintype.card (D.BBas (.inl (0, 0))) = 1 := Fintype.card_unit
  have hB2 : Fintype.card (D.BBas (.inr 0)) = 1 := by
    change Fintype.card D.Lab = 1; rw [ZMod.card]; omega
  have hbas : Fintype.card (D.Bas (.inr (.inl 0))) = 2 := by
    change Fintype.card (Option D.Lab) = 2; rw [Fintype.card_option, ZMod.card]; omega
  have hsum_lab : ∀ f : D.BBas (.inr 0) → ℂ, (∑ P : D.BBas (.inr 0), f P) = f b0 := fun f => by
    have hun : (Finset.univ : Finset (D.BBas (.inr 0))) = {b0} := by
      ext x; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact lab_eq_zero_of_q2 D hq2 x
    rw [hun, Finset.sum_singleton]
  rw [hsum_lab]; dsimp only
  have hutw : (utwW D) (.inr 0) (0, 0) b0 = 1 := by simp [utwW, b0]
  have hl1 : (labMu D) (.inr (.inl 0)) (.inl (0, 0)) u0 = some none := by simp [labMu]; rfl
  have hl2 : (labMu D) (.inr (.inl 0)) (.inr 0) b0 = some (some 0) := by
    simp [labMu, b0]; rfl
  rw [hutw, map_one, mul_one, hl1, hl2]
  unfold Rent
  rw [hbas, hB1, hB2]
  dsimp only [FieldData.R]
  simp only [Nat.cast_ofNat, Nat.cast_one]
  rw [show Real.sqrt (2 * (D.q : ℝ) / (1 * 1 * 1 * ((D.q : ℝ) + 1))) =
      Real.sqrt (2 * 2 / (1 * 1 * 1 * (2 + 1))) by rw [hq2]; norm_num]
  change (Real.sqrt (2 * 2 / (1 * 1 * 1 * (2 + 1))) : ℂ) *
      matEntry (D.psModel 0 0 ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq))
        (D.stVec 0 none) (D.wVec 0 0) = 1
  unfold matEntry
  simp_rw [wVec_0_q2 D hq2, sum_option_fq_q2 D hq2]
  have hnone : D.vT 1 none = 0 := rfl
  have hs0 : D.vT 1 (some 0) = FieldData.isqrt 2 := by simp [FieldData.vT, hq2, psi_zero]
  have hs1 : D.vT 1 (some 1) = -FieldData.isqrt 2 := by simp [FieldData.vT, hq2, psi_one_q2 D hq2]
  have hv_none : D.stVec 0 none none = FieldData.isqrt 3 * (Real.sqrt 2 : ℂ) := by
    simp only [FieldData.stVec, hq2, chi_zero_neg_one, Nat.cast_ofNat, mul_one]
    rw [show (2 : ℝ) + 1 = 3 by norm_num]
  have hv_0 : D.stVec 0 none (some 0) = -(FieldData.isqrt 3 * FieldData.isqrt 2) := by
    simp only [FieldData.stVec, hq2, Nat.cast_ofNat]
    rw [show (2 : ℝ) + 1 = 3 by norm_num]; ring
  have hv_1 : D.stVec 0 none (some 1) = -(FieldData.isqrt 3 * FieldData.isqrt 2) := by
    simp only [FieldData.stVec, hq2, Nat.cast_ofNat]
    rw [show (2 : ℝ) + 1 = 3 by norm_num]; ring
  have h01 : (0 : D.Fq) ≠ 1 := zero_ne_one
  have h10 : (1 : D.Fq) ≠ 0 := one_ne_zero
  simp only [hnone, hs0, hs1, mul_zero, add_zero, zero_add, psModel_00_wGL_apply,
    hv_none, hv_0, hv_1, if_pos rfl, if_neg h01, if_neg h10, inv_one, Option.some.injEq,
    ↓reduceIte, mul_one]
  have hring_real : ∀ r : ℝ, starRingEnd ℂ (r : ℂ) = (r : ℂ) := fun r => Complex.conj_ofReal r
  have hr : Real.sqrt (2 * 2 / (1 * (2 + 1))) *
      ((Real.sqrt 3)⁻¹ * Real.sqrt 2 * (Real.sqrt 2)⁻¹ +
       -((Real.sqrt 3)⁻¹ * (Real.sqrt 2)⁻¹) * -(Real.sqrt 2)⁻¹) = 1 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have hnum : Real.sqrt (2 * 2 / (1 * (2 + 1))) = 2 * (Real.sqrt 3)⁻¹ := by
      rw [show (2 : ℝ) * 2 / (1 * (2 + 1)) = 4 / 3 by norm_num, Real.sqrt_div (by norm_num),
        show Real.sqrt 4 = 2 by norm_num, div_eq_mul_inv]
    rw [hnum]
    have hp1 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hp3 : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
    nlinarith [h2, h3]
  simp only [FieldData.isqrt, map_neg, map_mul, hring_real]
  split_ifs
  all_goals first
    | contradiction
    | (simp only [mul_zero, zero_mul, add_zero, zero_add]; exact_mod_cast hr)

/-! ### Section 4: `Pre`, `Core`, and `Post` circuits for `D.q = 2` -/

abbrev Mid3 : Type := Bool × Bool × Qubits 1

def midCode3 : Mid3 → Qubits 3 :=
  boolAppCode (boolAppCode (fun q : Qubits 1 => q))

lemma midCode3_eq (b₀ b₁ : Bool) (b₂ : Qubits 1) :
    midCode3 (b₀, b₁, b₂) = ![b₀, b₁, b₂ 0] := by
  ext i; fin_cases i <;> rfl

def preMap (D : FieldData) (x : InReg D) : Mid3 :=
  let b₀ := match x.1.1 with | .inl _ => false | .inr _ => true
  let b₁ := match x.1.2.2.2 with | .inl _ => false | .inr _ => true
  (b₀, b₁, fun _ => if b₀ == b₁ then x.1.2.2.1 else false)

lemma preMap_injective (D : FieldData) (hq2 : D.q = 2) : Function.Injective (preMap D) := by
  intro x₁ x₂ heq
  apply Subtype.ext
  have h0 : (match x₁.1.1 with | .inl _ => false | .inr _ => true) =
      (match x₂.1.1 with | .inl _ => false | .inr _ => true) := congrArg Prod.fst heq
  have h1 : (match x₁.1.2.2.2 with | .inl _ => false | .inr _ => true) =
      (match x₂.1.2.2.2 with | .inl _ => false | .inr _ => true) := congrArg (fun p => p.2.1) heq
  have h2 : (if (match x₁.1.1 with | .inl _ => false | .inr _ => true) ==
        (match x₁.1.2.2.2 with | .inl _ => false | .inr _ => true) then x₁.1.2.2.1 else false) =
      (if (match x₂.1.1 with | .inl _ => false | .inr _ => true) ==
        (match x₂.1.2.2.2 with | .inl _ => false | .inr _ => true) then x₂.1.2.2.1 else false) :=
    congrFun (congrArg (fun p => p.2.2) heq) 0
  have hl : x₁.1.1 = x₂.1.1 := by
    rcases hx1 : x₁.1.1 with ⟨a1, b1⟩ | g1 <;> rcases hx2 : x₂.1.1 with ⟨a2, b2⟩ | g2 <;> simp_all
    · rw [lab_eq_zero_of_q2 D hq2 a1, lab_eq_zero_of_q2 D hq2 b1,
        lab_eq_zero_of_q2 D hq2 a2, lab_eq_zero_of_q2 D hq2 b2]
      exact ⟨rfl, rfl⟩
    · rw [lab_eq_zero_of_q2 D hq2 g1, lab_eq_zero_of_q2 D hq2 g2]
  have hlt : x₁.1.2.2.2 = x₂.1.2.2.2 := by
    rcases hx1 : x₁.1.2.2.2 with ⟨a1, b1⟩ | g1 <;> rcases hx2 : x₂.1.2.2.2 with ⟨a2, b2⟩ | g2 <;> simp_all
    · rw [lab_eq_zero_of_q2 D hq2 a1, lab_eq_zero_of_q2 D hq2 b1,
        lab_eq_zero_of_q2 D hq2 a2, lab_eq_zero_of_q2 D hq2 b2]
      exact ⟨rfl, rfl⟩
    · rw [lab_eq_zero_of_q2 D hq2 g1, lab_eq_zero_of_q2 D hq2 g2]
  have hw : x₁.1.2.2.1 = x₂.1.2.2.1 := by
    have hv1 := x₁.2; have hv2 := x₂.2
    unfold ValidIn at hv1 hv2
    cases hw1 : x₁.1.2.2.1 <;> cases hw2 : x₂.1.2.2.1
    · rfl
    · simp only [hw1, Bool.false_eq_true, ↓reduceIte] at hv1
      simp only [hw1, hw2] at h2
      rcases hv1 with ⟨_, heq1⟩
      rw [heq1, beq_self_eq_true, if_pos rfl] at h2
      rw [← hl, ← hlt, heq1, beq_self_eq_true, if_pos rfl] at h2
      exact absurd h2 Bool.false_ne_true
    · simp only [hw2, Bool.false_eq_true, ↓reduceIte] at hv2
      simp only [hw1, hw2] at h2
      rcases hv2 with ⟨_, heq2⟩
      rw [heq2, beq_self_eq_true, if_pos rfl] at h2
      rw [hl, hlt, heq2, beq_self_eq_true, if_pos rfl] at h2
      exact absurd h2 Bool.false_ne_true.symm
    · rfl
  have hk : x₁.1.2.1 = x₂.1.2.1 := by
    have hv1 := x₁.2; have hv2 := x₂.2
    unfold ValidIn at hv1 hv2
    cases hw1 : x₁.1.2.2.1
    · simp only [hw1, Bool.false_eq_true, ↓reduceIte] at hv1
      have hw2 : x₂.1.2.2.1 = false := hw.symm.trans hw1
      simp only [hw2, Bool.false_eq_true, ↓reduceIte] at hv2
      rw [hv1.1, hv2.1, hl]
    · simp only [hw1, ↓reduceIte] at hv1
      have hw2 : x₂.1.2.2.1 = true := hw.symm.trans hw1
      simp only [hw2, ↓reduceIte] at hv2
      rcases hv1 with ⟨ab1, hk1, _, _⟩
      rcases hv2 with ⟨ab2, hk2, _, _⟩
      have hab1 : ab1 = (0, 0) := Prod.ext (lab_eq_zero_of_q2 D hq2 _) (lab_eq_zero_of_q2 D hq2 _)
      have hab2 : ab2 = (0, 0) := Prod.ext (lab_eq_zero_of_q2 D hq2 _) (lab_eq_zero_of_q2 D hq2 _)
      rw [hk1, hk2, hab1, hab2]
  ext <;> simp [hl, hk, hw, hlt]

def preRev20 : List (RevGate 20) :=
  [ .cnot 14 1 (by decide), .cnot 1 14 (by decide),
    .cnot 12 2 (by decide), .cnot 2 12 (by decide),
    .x 2, .ccx 0 2 6 (by decide) (by decide) (by decide), .x 2,
    .cnot 0 2 (by decide), .cnot 1 2 (by decide) ]

def preCirc20 : List (Instr 20) := compileRev preRev20

lemma preRev20_eval_bools (b0 b1 w : Bool) (hneq : w = false → b0 = b1) :
    evalRev preRev20
        (fun j : Fin 20 => if j = 0 then b0 else if j = 6 then (if w then false else b0)
          else if j = 12 then w else if j = 14 then b1 else false) =
      padTo 20 (midCode3 (b0, b1, fun _ => if (b0 == b1) then w else false)) := by
  ext i
  fin_cases i <;> cases b0 <;> cases b1 <;> cases w <;>
    simp [preRev20, midCode3, padTo, boolAppCode, Fin.append, Fin.addCases,
      RevGate.eval] at * <;>
    exact absurd (hneq rfl) (by decide)

lemma preRev20_eval (D : FieldData) (hq2 : D.q = 2) (x : InReg D) :
    evalRev preRev20 (padTo 20 (inCodeA D x)) = padTo 20 (midCode3 (preMap D x)) := by
  have hlabW : D.labW = 2 := (q_eq_two_p_r D hq2).2.2
  have htest0 : ∀ a : D.Lab, ZMod.val a = 0 := fun a => by rw [lab_eq_zero_of_q2 D hq2 a]; exact ZMod.val_zero
  have hin : ∀ i : Fin 20, padTo 20 (inCodeA D x) i =
      if i = 0 then (match x.1.1 with | .inl _ => false | .inr _ => true)
      else if i = 6 then (match x.1.2.1 with | .inl _ => false | .inr _ => true)
      else if i = 12 then x.1.2.2.1
      else if i = 14 then (match x.1.2.2.2 with | .inl _ => false | .inr _ => true)
      else false := by
    intro i
    simp only [padTo, inCodeA, packNat, hlabW, dif_pos (by omega : i.val < 10 * 2)]
    fin_cases i <;> simp [birrFields]
    · cases x.1.1 <;> rfl
    · cases x.1.1 with | inl ab => simp [htest0 ab.1, Nat.testBit] | inr g => simp [Nat.testBit]
    · cases x.1.1 with | inl ab => simp [htest0 ab.1] | inr g => simp [htest0 g]
    · cases x.1.1 with | inl ab => simp [htest0 ab.1, Nat.testBit] | inr g => simp [htest0 g, Nat.testBit]
    · cases x.1.1 with | inl ab => simp [htest0 ab.2] | inr g => simp
    · cases x.1.1 with | inl ab => simp [htest0 ab.2, Nat.testBit] | inr g => simp [Nat.testBit]
    · cases x.1.2.1 <;> rfl
    · cases x.1.2.1 with | inl ab => simp [htest0 ab.1, Nat.testBit] | inr g => simp [Nat.testBit]
    · cases x.1.2.1 with | inl ab => simp [htest0 ab.1] | inr g => simp [htest0 g]
    · cases x.1.2.1 with | inl ab => simp [htest0 ab.1, Nat.testBit] | inr g => simp [htest0 g, Nat.testBit]
    · cases x.1.2.1 with | inl ab => simp [htest0 ab.2] | inr g => simp
    · cases x.1.2.1 with | inl ab => simp [htest0 ab.2, Nat.testBit] | inr g => simp [Nat.testBit]
    · cases x.1.2.2.1 <;> rfl
    · cases x.1.2.2.1 <;> simp [Nat.testBit]
    · cases x.1.2.2.2 <;> rfl
    · cases x.1.2.2.2 with | inl ab => simp [htest0 ab.1, Nat.testBit] | inr g => simp [Nat.testBit]
    · cases x.1.2.2.2 with | inl ab => simp [htest0 ab.1] | inr g => simp [htest0 g]
    · cases x.1.2.2.2 with | inl ab => simp [htest0 ab.1, Nat.testBit] | inr g => simp [htest0 g, Nat.testBit]
    · cases x.1.2.2.2 with | inl ab => simp [htest0 ab.2] | inr g => simp
    · cases x.1.2.2.2 with | inl ab => simp [htest0 ab.2, Nat.testBit] | inr g => simp [Nat.testBit]
  have hvalid : (match x.1.2.1 with | .inl _ => false | .inr _ => true) =
      if x.1.2.2.1 then false else (match x.1.1 with | .inl _ => false | .inr _ => true) := by
    have hv := x.2; unfold ValidIn at hv
    cases hw : x.1.2.2.1 <;> simp only [hw] at hv ⊢
    · simp [hv.1]
    · rcases hv with ⟨ab, hk, _, _⟩; simp [hk]
  have hneq : x.1.2.2.1 = false →
      (match x.1.1 with | .inl _ => false | .inr _ => true) =
      (match x.1.2.2.2 with | .inl _ => false | .inr _ => true) := by
    intro hw; have hv := x.2; unfold ValidIn at hv; simp [hw] at hv; rw [hv.2]
  rw [show padTo 20 (inCodeA D x) = (fun j : Fin 20 =>
      if j = 0 then (match x.1.1 with | .inl _ => false | .inr _ => true)
      else if j = 6 then (if x.1.2.2.1 then false else (match x.1.1 with | .inl _ => false | .inr _ => true))
      else if j = 12 then x.1.2.2.1
      else if j = 14 then (match x.1.2.2.2 with | .inl _ => false | .inr _ => true)
      else false) from funext fun j => by rw [hin j, hvalid]]
  exact preRev20_eval_bools _ _ _ hneq

def postMap (D : FieldData) (hq2 : D.q = 2) (s : Mid3) : OutReg D :=
  let b₀ := s.1
  let b₁ := s.2.1
  let b₂ := s.2.2 0
  (if b₀ then .inr 0 else .inl (0, 0),
   if b₂ then (if b₀ && b₁ then .inr (.inr (.inr (cusp1 D hq2))) else .inl 0) else .inr (.inl 0),
   if b₁ then .inr 0 else .inl (0, 0))

lemma postMap_injective (D : FieldData) (hq2 : D.q = 2) : Function.Injective (postMap D hq2) := by
  intro s₁ s₂ heq
  rcases s₁ with ⟨a1, b1, c1⟩
  rcases s₂ with ⟨a2, b2, c2⟩
  have h1 : (if a1 then (Sum.inr 0 : D.BIrr) else Sum.inl (0, 0)) = if a2 then .inr 0 else .inl (0, 0) :=
    congrArg Prod.fst heq
  have h2 : (if b1 then (Sum.inr 0 : D.BIrr) else Sum.inl (0, 0)) = if b2 then .inr 0 else .inl (0, 0) :=
    congrArg (fun y => y.2.2) heq
  have hμ : (if c1 0 then (if a1 && b1 then (Sum.inr (.inr (.inr (cusp1 D hq2))) : D.Irr) else Sum.inl 0)
        else Sum.inr (.inl 0)) =
      if c2 0 then (if a2 && b2 then .inr (.inr (.inr (cusp1 D hq2))) else .inl 0) else .inr (.inl 0) :=
    congrArg (fun y => y.2.1) heq
  have ha : a1 = a2 := by cases a1 <;> cases a2 <;> simp_all
  have hb : b1 = b2 := by cases b1 <;> cases b2 <;> simp_all
  have hc0 : c1 0 = c2 0 := by
    cases hc1 : c1 0 <;> cases hc2 : c2 0 <;> simp_all
    all_goals (split_ifs at hμ <;> simp_all)
  have hc : c1 = c2 := funext fun k => by fin_cases k; exact hc0
  simp [ha, hb, hc]

def postRev18 : List (RevGate 18) :=
  [ .cnot 1 12 (by decide), .cnot 12 1 (by decide),
    .ccx 0 12 1 (by decide) (by decide) (by decide),
    .ccx 1 2 7 (by decide) (by decide) (by decide),
    .ccx 0 12 1 (by decide) (by decide) (by decide),
    .cnot 7 8 (by decide),
    .x 2, .cnot 2 6 (by decide), .cnot 7 6 (by decide), .x 2,
    .x 6, .cnot 6 2 (by decide), .cnot 7 2 (by decide), .x 6 ]

def postCirc18 : List (Instr 18) := compileRev postRev18

private lemma postRev18_eval_bools (b0 b1 b2 : Bool) :
    evalRev postRev18
      (fun j : Fin 18 => if j = 0 then b0 else if j = 1 then b1 else if j = 2 then b2 else false) =
      (fun j : Fin 18 =>
        if j = 0 then b0
        else if j = 6 then ((!b2) != (b0 && b1 && b2))
        else if j = 7 then (b0 && b1 && b2)
        else if j = 8 then (b0 && b1 && b2)
        else if j = 12 then b1
        else false) := by
  ext j
  fin_cases j <;> cases b0 <;> cases b1 <;> cases b2 <;> decide

lemma postRev18_eval (D : FieldData) (hq2 : D.q = 2) (s : Mid3) :
    evalRev postRev18 (padTo 18 (midCode3 s)) = padTo 18 (outCodeA D (postMap D hq2 s)) := by
  have hlabW : D.labW = 2 := (q_eq_two_p_r D hq2).2.2
  have hc1 : (cusp1 D hq2).1.val = 1 := by
    have : NeZero (D.q ^ 2 - 1) := ⟨by rw [hq2]; decide⟩
    have : Fact (1 < D.q ^ 2 - 1) := ⟨by rw [hq2]; decide⟩
    change (1 : D.Lab2).val = 1
    exact ZMod.val_one (D.q ^ 2 - 1)
  have h0val : (0 : D.Lab).val = 0 := ZMod.val_zero
  rcases s with ⟨b0, b1, b2⟩
  have hmid : padTo 18 (midCode3 (b0, b1, b2)) =
      (fun j : Fin 18 => if j = 0 then b0 else if j = 1 then b1 else if j = 2 then b2 0 else false) := by
    funext i
    fin_cases i <;> simp [midCode3, padTo, boolAppCode, Fin.append, Fin.addCases]
  have hout : (fun j : Fin 18 =>
        if j = 0 then b0
        else if j = 6 then ((!(b2 0)) != (b0 && b1 && b2 0))
        else if j = 7 then (b0 && b1 && b2 0)
        else if j = 8 then (b0 && b1 && b2 0)
        else if j = 12 then b1
        else false) =
      padTo 18 (outCodeA D (postMap D hq2 (b0, b1, b2))) := by
    funext i
    have hi : i.val < 9 * D.labW := by rw [hlabW]; exact i.isLt
    simp only [padTo, dif_pos hi, outCodeA, packNat, hlabW, postMap]
    fin_cases i <;> cases b0 <;> cases b1 <;> cases hb2 : b2 0 <;>
      (simp [birrFields, FieldData.irrFields, hc1, h0val, hb2]; try decide)
  rw [hmid, postRev18_eval_bools, hout]

def matZ : Matrix (Qubits 1) (Qubits 1) ℂ :=
  Matrix.diagonal fun q => if q 0 then (-1 : ℂ) else 1

lemma circUnitary_z : circUnitary ([.s 0, .s 0] : List (Instr 1)) = matZ := by
  have h : ([.s 0, .s 0] : List (Instr 1)) = [.s 0] ++ [.s 0] := rfl
  rw [h, circUnitary_append, instr_s_unitary]
  ext y z
  by_cases hyz : y = z
  · subst hyz; cases hy : y 0 <;> simp [matZ, hy]
  · simp [matZ, hyz]

lemma midCore_apply (D : FieldData) (z x : Mid3) :
    ctrlMat (ctrlMat (U_q D) 1) (ctrlMat 1 (U_q D * matZ)) z x =
      if z.1 = x.1 ∧ z.2.1 = x.2.1 then
        match z.1, z.2.1 with
        | false, false => U_q D z.2.2 x.2.2
        | false, true  => if z.2.2 = x.2.2 then 1 else 0
        | true,  false => if z.2.2 = x.2.2 then 1 else 0
        | true,  true  => (U_q D * matZ) z.2.2 x.2.2
      else 0 := by
  rcases z with ⟨z0, z1, z2⟩; rcases x with ⟨x0, x1, x2⟩
  cases z0 <;> cases z1 <;> cases x0 <;> cases x1 <;>
    simp [ctrlMat, Matrix.of_apply, Matrix.one_apply]

lemma Uq_mul_matZ_apply (D : FieldData) (y x : Qubits 1) :
    (U_q D * matZ) y x = (if x 0 then -1 else 1) * U_q D y x := by
  have hx0 : x = fun _ => x 0 := funext fun i => by fin_cases i; rfl
  rw [hx0]
  cases hb : x 0 <;> simp [Matrix.mul_apply, matZ, Matrix.diagonal_apply, sum_qubits1]

private lemma det_inr_zero (D : FieldData) (a : D.Lab) (l lt κ : D.BIrr) (ω : Bool)
    (hor : l = .inr 0 ∨ lt = .inr 0) : A70 D l lt κ ω (.inl a) = 0 := by
  unfold A70
  cases ω
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with hd
    · rcases hor with rfl | rfl
      · simp [labMu, Rent.eq_def]
      · rw [hd.2] at *; simp [labMu, Rent.eq_def]
    · rfl
  · simp only [↓reduceIte]
    cases κ with
    | inr _ => rfl
    | inl ab =>
      have hzeroR : ∀ o P, Rent D (.inl a) (wGL D) o ((labMu D) (.inl a) (.inr 0) P) = 0 := by
        intro o P; cases o <;> simp [labMu, Rent.eq_def]
      have hzeroL : ∀ P o, Rent D (.inl a) (wGL D) ((labMu D) (.inl a) (.inr 0) P) o = 0 := by
        intro P o; cases o <;> simp [labMu, Rent.eq_def]
      rcases hor with rfl | rfl
      · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun P _ => ?_)
        cases (tLab D) lt ab with
        | none => simp
        | some Pt => dsimp only; rw [hzeroR _ P, zero_mul]
      · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun P _ => ?_)
        cases (tLab D) (.inr 0) ab with
        | none => simp
        | some Pt => dsimp only; rw [hzeroL Pt _, zero_mul]

private lemma cusp_inl_zero (D : FieldData) (k : {k : D.Lab2 // D.IsCuspLabel k})
    (l lt κ : D.BIrr) (ω : Bool) (hor : l = .inl (0, 0) ∨ lt = .inl (0, 0)) :
    A70 D l lt κ ω (.inr (.inr (.inr k))) = 0 := by
  unfold A70
  cases ω
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with hd
    · rcases hor with rfl | rfl
      · simp [labMu, Rent.eq_def]
      · rw [hd.2] at *; simp [labMu, Rent.eq_def]
    · rfl
  · simp only [↓reduceIte]
    cases κ with
    | inr _ => rfl
    | inl ab =>
      have hzeroR : ∀ o P, Rent D (.inr (.inr (.inr k))) (wGL D) o
          ((labMu D) (.inr (.inr (.inr k))) (.inl (0, 0)) P) = 0 := by
        intro o P; cases o <;> simp [labMu, Rent.eq_def]
      have hzeroL : ∀ P o, Rent D (.inr (.inr (.inr k))) (wGL D)
          ((labMu D) (.inr (.inr (.inr k))) (.inl (0, 0)) P) o = 0 := by
        intro P o; cases o <;> simp [labMu, Rent.eq_def]
      rcases hor with rfl | rfl
      · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun P _ => ?_)
        cases (tLab D) lt ab with
        | none => simp
        | some Pt => dsimp only; rw [hzeroR _ P, zero_mul]
      · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun P _ => ?_)
        cases (tLab D) (.inl (0, 0)) ab with
        | none => simp
        | some Pt => dsimp only; rw [hzeroL Pt _, zero_mul]

private lemma postMap_ne_cusp_l_inl (D : FieldData) (hq2 : D.q = 2)
    (k : {k : D.Lab2 // D.IsCuspLabel k}) (lt : D.BIrr) :
    ¬ ∃ z, postMap D hq2 z = (.inl (0, 0), .inr (.inr (.inr k)), lt) := by
  rintro ⟨⟨z0, z1, z2⟩, hz⟩
  simp only [postMap, Prod.mk.injEq] at hz
  rcases hz with ⟨hz0, hμ, _⟩
  cases z0 <;> cases z1 <;> cases hz2 : z2 0 <;> simp [hz2] at hz0 hμ

private lemma postMap_ne_cusp_lt_inl (D : FieldData) (hq2 : D.q = 2)
    (k : {k : D.Lab2 // D.IsCuspLabel k}) (l : D.BIrr) :
    ¬ ∃ z, postMap D hq2 z = (l, .inr (.inr (.inr k)), .inl (0, 0)) := by
  rintro ⟨⟨z0, z1, z2⟩, hz⟩
  simp only [postMap, Prod.mk.injEq] at hz
  rcases hz with ⟨_, hμ, hz1⟩
  cases z0 <;> cases z1 <;> cases hz2 : z2 0 <;> simp [hz2] at hz1 hμ

private lemma postMap_ne_det_inr (D : FieldData) (hq2 : D.q = 2) (a : D.Lab) :
    ¬ ∃ z, postMap D hq2 z = (.inr 0, .inl a, .inr 0) := by
  rintro ⟨⟨z0, z1, z2⟩, hz⟩
  simp only [postMap, Prod.mk.injEq] at hz
  rcases hz with ⟨hz0, hμ, hz1⟩
  cases z0 <;> cases z1 <;> cases hz2 : z2 0 <;> simp [hz2] at hz0 hz1 hμ

lemma coreMat_eq_totalA (D : FieldData) (hq2 : D.q = 2) :
    permMat (postMap D hq2) * (ctrlMat (ctrlMat (U_q D) 1) (ctrlMat 1 (U_q D * matZ)) * permMat (preMap D)) =
      totalA D := by
  ext y x
  have hmul_right : ∀ z : Mid3,
      (ctrlMat (ctrlMat (U_q D) 1) (ctrlMat 1 (U_q D * matZ)) * permMat (preMap D)) z x =
        ctrlMat (ctrlMat (U_q D) 1) (ctrlMat 1 (U_q D * matZ)) z (preMap D x) := by
    intro z
    simp only [Matrix.mul_apply, permMat, Matrix.of_apply]
    rw [Finset.sum_eq_single (preMap D x)]
    · simp
    · intro u _ hu; simp [hu]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [Matrix.mul_apply]
  have hsum_mid : (∑ z : Mid3, permMat (postMap D hq2) y z *
      (ctrlMat (ctrlMat (U_q D) 1) (ctrlMat 1 (U_q D * matZ)) * permMat (preMap D)) z x) =
      if h : ∃ z, postMap D hq2 z = y then
        ctrlMat (ctrlMat (U_q D) 1) (ctrlMat 1 (U_q D * matZ)) h.choose (preMap D x)
      else 0 := by
    split_ifs with hex
    · rw [Finset.sum_eq_single hex.choose]
      · simp only [permMat, Matrix.of_apply]
        rw [if_pos hex.choose_spec.symm, one_mul]
        exact hmul_right hex.choose
      · intro z _ hz
        have hne : y ≠ postMap D hq2 z := fun heq =>
          hz ((postMap_injective D hq2) (hex.choose_spec.trans heq).symm)
        simp only [permMat, Matrix.of_apply, if_neg hne, zero_mul]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · refine Finset.sum_eq_zero fun z _ => ?_
      have hne : y ≠ postMap D hq2 z := fun heq => hex ⟨z, heq.symm⟩
      simp only [permMat, Matrix.of_apply, if_neg hne, zero_mul]
  rw [hsum_mid]
  rcases y with ⟨ly, μ, lty⟩
  have hA := A70_small_blocks D
  have hsm := hA.2.1 0
  have hq2_sm := hA.2.2 hq2
  have hl_eq : x.1.1 = .inl (0, 0) ∨ x.1.1 = .inr 0 := by
    rcases hx : x.1.1 with ⟨a, b⟩ | g
    · left; rw [lab_eq_zero_of_q2 D hq2 a, lab_eq_zero_of_q2 D hq2 b]
    · right; rw [lab_eq_zero_of_q2 D hq2 g]
  have hlt_eq : x.1.2.2.2 = .inl (0, 0) ∨ x.1.2.2.2 = .inr 0 := by
    rcases hx : x.1.2.2.2 with ⟨a, b⟩ | g
    · left; rw [lab_eq_zero_of_q2 D hq2 a, lab_eq_zero_of_q2 D hq2 b]
    · right; rw [lab_eq_zero_of_q2 D hq2 g]
  have hμ_cases : (∃ a, μ = .inl a) ∨ (∃ a, μ = .inr (.inl a)) ∨ (∃ k, μ = .inr (.inr (.inr k))) := by
    rcases μ with a | a | ab | k
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl ⟨a, rfl⟩)
    · exfalso; have h1 := lab_eq_zero_of_q2 D hq2 ab.1.1; have h2 := lab_eq_zero_of_q2 D hq2 ab.1.2
      have := ab.2; rw [h1, h2] at this; exact Nat.lt_irrefl _ this
    · exact Or.inr (Or.inr ⟨k, rfl⟩)
  have hk_false : x.1.2.2.1 = false → x.1.2.1 = x.1.1 ∧ x.1.2.2.2 = x.1.1 := by
    intro hw; have hv := x.2; unfold ValidIn at hv; simpa [hw] using hv
  have hk_true : x.1.2.2.1 = true → x.1.2.1 = .inl (0, 0) := by
    intro hw; have hv := x.2; unfold ValidIn at hv; simp only [hw, ↓reduceIte] at hv
    rcases hv with ⟨ab, hk_eq, _, _⟩
    rw [hk_eq, show ab = (0, 0) from Prod.ext (lab_eq_zero_of_q2 D hq2 _) (lab_eq_zero_of_q2 D hq2 _)]
  have hpre_l : (if (preMap D x).1 then (Sum.inr 0 : D.BIrr) else Sum.inl (0, 0)) = x.1.1 := by
    rcases hl_eq with h | h <;> simp [preMap, h]
  have hpre_lt : (if (preMap D x).2.1 then (Sum.inr 0 : D.BIrr) else Sum.inl (0, 0)) = x.1.2.2.2 := by
    rcases hlt_eq with h | h <;> simp [preMap, h]
  by_cases hdiag : ly = x.1.1 ∧ lty = x.1.2.2.2
  · rw [hdiag.1, hdiag.2, totalA, Matrix.of_apply, if_pos ⟨rfl, rfl⟩]
    rcases hl_eq with hl0 | hl0 <;> rcases hlt_eq with hlt0 | hlt0 <;> rw [hl0, hlt0]
    · -- Case 1: l = inl (0, 0), lt = inl (0, 0)
      rcases hμ_cases with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨k, rfl⟩
      · rw [lab_eq_zero_of_q2 D hq2 a]
        have hz_ex : ∃ z, postMap D hq2 z = (.inl (0, 0), .inl 0, .inl (0, 0)) :=
          ⟨(false, false, fun _ => true), by simp [postMap]⟩
        rw [dif_pos hz_ex]
        have hcz := postMap_injective D hq2
          (hz_ex.choose_spec.trans (show postMap D hq2 (false, false, fun _ => true) = _ by simp [postMap]).symm)
        rw [hcz, midCore_apply]
        cases hw : x.1.2.2.1
        · obtain ⟨hk, _⟩ := hk_false hw
          rw [hk, hl0]; simp [preMap, hl0, hlt0, hw, U_q, hsm.2.1, hq2]
        · rw [hk_true hw]; simp [preMap, hl0, hlt0, hw, U_q, hsm.2.2.2, chi_zero_neg_one, hq2]
      · rw [lab_eq_zero_of_q2 D hq2 a]
        have hz_ex : ∃ z, postMap D hq2 z = (.inl (0, 0), .inr (.inl 0), .inl (0, 0)) :=
          ⟨(false, false, fun _ => false), by simp [postMap]⟩
        rw [dif_pos hz_ex]
        have hcz := postMap_injective D hq2
          (hz_ex.choose_spec.trans (show postMap D hq2 (false, false, fun _ => false) = _ by simp [postMap]).symm)
        rw [hcz, midCore_apply]
        cases hw : x.1.2.2.1
        · obtain ⟨hk, _⟩ := hk_false hw
          rw [hk, hl0]; simp [preMap, hl0, hlt0, hw, U_q, hsm.1, hq2]
        · rw [hk_true hw]; simp [preMap, hl0, hlt0, hw, U_q, hsm.2.2.1, chi_zero_neg_one, hq2]
      · rw [cusp_inl_zero D k _ _ _ _ (Or.inl rfl), dif_neg (postMap_ne_cusp_l_inl D hq2 k _)]
    · -- Case 2: l = inl (0, 0), lt = inr 0
      have hw : x.1.2.2.1 = true := by
        by_contra hnf; have hff := Bool.eq_false_iff.mpr hnf
        have := (hk_false hff).2; simp [hl0, hlt0] at this
      rcases hμ_cases with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨k, rfl⟩
      · rw [lab_eq_zero_of_q2 D hq2 a, det_inr_zero D 0 _ _ _ _ (Or.inr rfl)]
        have hz_ex : ∃ z, postMap D hq2 z = (.inl (0, 0), .inl 0, .inr 0) :=
          ⟨(false, true, fun _ => true), by simp [postMap]⟩
        rw [dif_pos hz_ex]
        have hcz := postMap_injective D hq2
          (hz_ex.choose_spec.trans (show postMap D hq2 (false, true, fun _ => true) = _ by simp [postMap]).symm)
        rw [hcz, midCore_apply]; simp [preMap, hl0, hlt0]
        exact fun h => Bool.false_ne_true (congrFun h 0).symm
      · rw [lab_eq_zero_of_q2 D hq2 a, hk_true hw, hw, A70_off_q2_left D hq2]
        have hz_ex : ∃ z, postMap D hq2 z = (.inl (0, 0), .inr (.inl 0), .inr 0) :=
          ⟨(false, true, fun _ => false), by simp [postMap]⟩
        rw [dif_pos hz_ex]
        have hcz := postMap_injective D hq2
          (hz_ex.choose_spec.trans (show postMap D hq2 (false, true, fun _ => false) = _ by simp [postMap]).symm)
        rw [hcz, midCore_apply]; simp [preMap, hl0, hlt0]
      · rw [cusp_inl_zero D k _ _ _ _ (Or.inl rfl), dif_neg (postMap_ne_cusp_l_inl D hq2 k _)]
    · -- Case 3: l = inr 0, lt = inl (0, 0)
      have hw : x.1.2.2.1 = true := by
        by_contra hnf; have hff := Bool.eq_false_iff.mpr hnf
        have := (hk_false hff).2; simp [hl0, hlt0] at this
      rcases hμ_cases with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨k, rfl⟩
      · rw [lab_eq_zero_of_q2 D hq2 a, det_inr_zero D 0 _ _ _ _ (Or.inl rfl)]
        have hz_ex : ∃ z, postMap D hq2 z = (.inr 0, .inl 0, .inl (0, 0)) :=
          ⟨(true, false, fun _ => true), by simp [postMap]⟩
        rw [dif_pos hz_ex]
        have hcz := postMap_injective D hq2
          (hz_ex.choose_spec.trans (show postMap D hq2 (true, false, fun _ => true) = _ by simp [postMap]).symm)
        rw [hcz, midCore_apply]; simp [preMap, hl0, hlt0]
        exact fun h => Bool.false_ne_true (congrFun h 0).symm
      · rw [lab_eq_zero_of_q2 D hq2 a, hk_true hw, hw, A70_off_q2_right D hq2]
        have hz_ex : ∃ z, postMap D hq2 z = (.inr 0, .inr (.inl 0), .inl (0, 0)) :=
          ⟨(true, false, fun _ => false), by simp [postMap]⟩
        rw [dif_pos hz_ex]
        have hcz := postMap_injective D hq2
          (hz_ex.choose_spec.trans (show postMap D hq2 (true, false, fun _ => false) = _ by simp [postMap]).symm)
        rw [hcz, midCore_apply]; simp [preMap, hl0, hlt0]
      · rw [cusp_inl_zero D k _ _ _ _ (Or.inr rfl), dif_neg (postMap_ne_cusp_lt_inl D hq2 k _)]
    · -- Case 4: l = inr 0, lt = inr 0
      rcases hμ_cases with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨k, rfl⟩
      · rw [det_inr_zero D a _ _ _ _ (Or.inl rfl), dif_neg (postMap_ne_det_inr D hq2 a)]
      · rw [lab_eq_zero_of_q2 D hq2 a]
        have hz_ex : ∃ z, postMap D hq2 z = (.inr 0, .inr (.inl 0), .inr 0) :=
          ⟨(true, true, fun _ => false), by simp [postMap]⟩
        rw [dif_pos hz_ex]
        have hcz := postMap_injective D hq2
          (hz_ex.choose_spec.trans (show postMap D hq2 (true, true, fun _ => false) = _ by simp [postMap]).symm)
        rw [hcz, midCore_apply]
        cases hw : x.1.2.2.1
        · obtain ⟨hk, _⟩ := hk_false hw
          rw [hk, hl0]; simp only [preMap, hl0, hlt0, hw]
          rw [Uq_mul_matZ_apply]
          simp [U_q, hq2_sm.1, hq2]
          rw [show (2 : ℝ) + 1 = 3 by norm_num]
        · rw [hk_true hw]; simp only [preMap, hl0, hlt0, hw]
          rw [Uq_mul_matZ_apply]
          simp [U_q, hq2_sm.2.1, hq2]
          rw [show (2 : ℝ) + 1 = 3 by norm_num]
      · rw [cusp_eq_cusp1_q2 D hq2 k]
        have hz_ex : ∃ z, postMap D hq2 z = (.inr 0, .inr (.inr (.inr (cusp1 D hq2))), .inr 0) :=
          ⟨(true, true, fun _ => true), by simp [postMap]⟩
        rw [dif_pos hz_ex]
        have hcz := postMap_injective D hq2
          (hz_ex.choose_spec.trans (show postMap D hq2 (true, true, fun _ => true) = _ by simp [postMap]).symm)
        rw [hcz, midCore_apply]
        cases hw : x.1.2.2.1
        · obtain ⟨hk, _⟩ := hk_false hw
          rw [hk, hl0]; simp only [preMap, hl0, hlt0, hw]
          rw [Uq_mul_matZ_apply]
          simp [U_q, (hq2_sm.2.2 (cusp1 D hq2)).1, hq2]
          rw [show (2 : ℝ) + 1 = 3 by norm_num]
        · rw [hk_true hw]; simp only [preMap, hl0, hlt0, hw]
          rw [Uq_mul_matZ_apply]
          simp [U_q, (hq2_sm.2.2 (cusp1 D hq2)).2, hq2]
          rw [show (2 : ℝ) + 1 = 3 by norm_num]
  · -- Off-block cases: all 12 vanish simultaneously!
    rw [totalA, Matrix.of_apply, if_neg (fun h => hdiag h)]
    split_ifs with hex
    · have hz := hex.choose_spec
      have hzl : (if hex.choose.1 then (Sum.inr 0 : D.BIrr) else Sum.inl (0, 0)) = ly :=
        congrArg Prod.fst hz
      have hzlt : (if hex.choose.2.1 then (Sum.inr 0 : D.BIrr) else Sum.inl (0, 0)) = lty :=
        congrArg (fun p => p.2.2) hz
      rw [midCore_apply, if_neg (fun ⟨he1, he2⟩ =>
        hdiag ⟨by rw [← hzl, he1, hpre_l], by rw [← hzlt, he2, hpre_lt]⟩)]
    · rfl

lemma poly_const_str (s : List Bool) : PolyTimeComputable (fun _ : Str => s) := by
  have h : Automatic.Poly (fun _ : List Bool => s) := by fun_prop
  rcases h with ⟨P⟩
  exact ⟨((BooleanLists.packProgram.comp P).comp BooleanLists.unpackProgram).stock⟩

lemma impl_const_id (P : FieldData → Prop) :
    UniformlyImplementsOn P (fun _ (x : Qubits 1) => x) (fun _ (y : Qubits 1) => y) (fun _ => 1) := by
  refine ⟨fun _ _ => 1, fun _ _ => [], fun _ => encNat 1 ++ encLayer ([] : List (Instr 1)), 1,
    poly_const_str _, fun _ _ _ => rfl, fun _ _ _ => by simp, fun _ _ k => ?_⟩
  refine ⟨le_rfl, le_rfl, fun ψ => ?_⟩
  have hpad : (fun x : Qubits 1 => padTo 1 x) = id := by
    funext x i; fin_cases i; simp [padTo]
  have hemb : ∀ v : EuclideanSpace ℂ (Qubits 1), embedVec id v = v := by
    intro v; apply WithLp.ofLp_injective; funext q
    simp [embedVec]
  rw [hpad, circUnitary_nil]
  change ‖act 1 (embedVec id ψ) - embedVec id (WithLp.toLp 2 ((1 : Matrix (Qubits 1) (Qubits 1) ℂ).mulVec (WithLp.ofLp ψ)))‖ ≤ _
  rw [hemb, hemb]
  have ha1 : act (1 : Matrix (Qubits 1) (Qubits 1) ℂ) ψ = ψ := by
    apply WithLp.ofLp_injective; simp [act]
  have hm1 : WithLp.toLp 2 ((1 : Matrix (Qubits 1) (Qubits 1) ℂ).mulVec (WithLp.ofLp ψ)) = ψ := by
    apply WithLp.ofLp_injective; simp
  rw [ha1, hm1, sub_self, norm_zero]
  positivity

lemma impl_matZ (P : FieldData → Prop) :
    UniformlyImplementsOn P (fun _ (x : Qubits 1) => x) (fun _ (y : Qubits 1) => y) (fun _ => matZ) := by
  refine ⟨fun _ _ => 1, fun _ _ => [.s 0, .s 0],
    fun _ => encNat 1 ++ encLayer ([.s 0, .s 0] : List (Instr 1)), 2,
    poly_const_str _, fun _ _ _ => rfl, fun D _ k => ?_, fun _ _ k => ?_⟩
  · have : 2 ≤ 2 * (Nat.log 2 D.q + k + 2) ^ 2 := by
      have : 4 ≤ (Nat.log 2 D.q + k + 2) ^ 2 := by
        have := Nat.pow_le_pow_left (by omega : 2 ≤ Nat.log 2 D.q + k + 2) 2; omega
      omega
    simpa using this
  · refine ⟨le_rfl, le_rfl, fun ψ => ?_⟩
    have hpad : (fun x : Qubits 1 => padTo 1 x) = id := by
      funext x i; fin_cases i; simp [padTo]
    have hemb : ∀ v : EuclideanSpace ℂ (Qubits 1), embedVec id v = v := by
      intro v; apply WithLp.ofLp_injective; funext q; simp [embedVec]
    rw [hpad, circUnitary_z]
    change ‖act matZ (embedVec id ψ) - embedVec id (WithLp.toLp 2 (matZ.mulVec (WithLp.ofLp ψ)))‖ ≤ _
    rw [hemb, hemb]
    have hact : act matZ ψ = WithLp.toLp 2 (matZ.mulVec (WithLp.ofLp ψ)) := rfl
    rw [hact, sub_self, norm_zero]; positivity

private lemma ccx3_len_le : ccx3.length ≤ 40 := by decide

private lemma pre20_impl :
    UniformlyImplementsOn (fun D => D.q = 2) (fun D => inCodeA D) (fun _ => midCode3)
      (fun D => permMat (preMap D)) := by
  refine ⟨fun _ _ => 20, fun _ _ => preCirc20,
    fun _ => encNat 20 ++ encLayer preCirc20, 10,
    poly_const_str _, fun _ _ _ => rfl, fun D _ k => ?_, fun D hq2 k => ?_⟩
  · have h1 := compileRev_length_le preRev20
    have h2 : preRev20.length = 9 := rfl
    have h3 := ccx3_len_le
    have hlen : preCirc20.length ≤ 400 := by
      rw [preCirc20]; exact h1.trans (by rw [h2]; omega)
    have hp : 2 ≤ Nat.log 2 D.q + k + 2 := by omega
    have hpow : 400 ≤ 10 * (Nat.log 2 D.q + k + 2) ^ 10 := by
      have h10 : 2 ^ 10 ≤ (Nat.log 2 D.q + k + 2) ^ 10 := Nat.pow_le_pow_left hp 10
      have h1024 : 400 ≤ 10 * 2 ^ 10 := by norm_num
      omega
    exact hlen.trans hpow
  · have hw2 : D.labW = 2 := (q_eq_two_p_r D hq2).2.2
    refine ⟨by dsimp only; rw [hw2], by dsimp only; omega, ?_⟩
    dsimp only
    rw [preCirc20, circUnitary_compileRev]
    convert @implements_of_act_ket_perm (InReg D) Mid3 _ _ 20 (permMat (evalRev preRev20))
      (fun x => padTo 20 (inCodeA D x)) (fun y => padTo 20 (midCode3 y)) (preMap D)
      (fun x => by rw [act_permMat, preRev20_eval D hq2 x]) ((1 / 2 : ℝ) ^ k) (by positivity)

private lemma post18_impl :
    UniformlyImplementsOn (fun D => D.q = 2) (fun _ => midCode3) (fun D => outCodeA D)
      (fun D => if h : D.q = 2 then permMat (postMap D h) else 0) := by
  refine ⟨fun _ _ => 18, fun _ _ => postCirc18,
    fun _ => encNat 18 ++ encLayer postCirc18, 10,
    poly_const_str _, fun _ _ _ => rfl, fun D _ k => ?_, fun D hq2 k => ?_⟩
  · have h1 := compileRev_length_le postRev18
    have h2 : postRev18.length = 14 := rfl
    have h3 := ccx3_len_le
    have hlen : postCirc18.length ≤ 600 := by
      rw [postCirc18]; exact h1.trans (by rw [h2]; omega)
    have hp : 2 ≤ Nat.log 2 D.q + k + 2 := by omega
    have hpow : 600 ≤ 10 * (Nat.log 2 D.q + k + 2) ^ 10 := by
      have h10 : 2 ^ 10 ≤ (Nat.log 2 D.q + k + 2) ^ 10 := Nat.pow_le_pow_left hp 10
      have h1024 : 600 ≤ 10 * 2 ^ 10 := by norm_num
      omega
    exact hlen.trans hpow
  · have hw2 : D.labW = 2 := (q_eq_two_p_r D hq2).2.2
    refine ⟨by dsimp only; omega, by dsimp only; rw [hw2], ?_⟩
    dsimp only
    rw [dif_pos hq2, postCirc18, circUnitary_compileRev]
    convert @implements_of_act_ket_perm Mid3 (OutReg D) _ _ 18 (permMat (evalRev postRev18))
      (fun s => padTo 18 (midCode3 s)) (fun y => padTo 18 (outCodeA D y)) (postMap D hq2)
      (fun s => by rw [act_permMat, postRev18_eval D hq2 s]) ((1 / 2 : ℝ) ^ k) (by positivity)

private lemma ctrlMat_iso {A : Type} [Fintype A] [DecidableEq A]
    (Φ₀ Φ₁ : Matrix A A ℂ) (h0 : Φ₀.conjTranspose * Φ₀ = 1) (h1 : Φ₁.conjTranspose * Φ₁ = 1) :
    (ctrlMat Φ₀ Φ₁).conjTranspose * ctrlMat Φ₀ Φ₁ = 1 := by
  ext y₁ y₂
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ctrlMat, Matrix.of_apply, Matrix.one_apply,
    RCLike.star_def]
  rw [Fintype.sum_prod_type]
  cases hb1 : y₁.1 <;> cases hb2 : y₂.1
  · have h0e := congrArg (fun M : Matrix A A ℂ => M y₁.2 y₂.2) h0
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, RCLike.star_def] at h0e
    simp [hb1, hb2, h0e, Prod.ext_iff]
  · simp [hb1, hb2, Prod.ext_iff]
  · simp [hb1, hb2, Prod.ext_iff]
  · have h1e := congrArg (fun M : Matrix A A ℂ => M y₁.2 y₂.2) h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, RCLike.star_def] at h1e
    simp [hb1, hb2, h1e, Prod.ext_iff]

private lemma matZ_iso : matZ.conjTranspose * matZ = 1 := by
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_eq_single a]
  · simp only [Matrix.conjTranspose_apply, matZ, Matrix.diagonal_apply,
      Matrix.one_apply, RCLike.star_def]
    by_cases hab : a = b
    · subst hab; cases a 0 <;> simp
    · simp [hab]
  · intro c hca
    simp [Matrix.conjTranspose_apply, matZ, Matrix.diagonal_apply, hca]

end GL2QFT_TotalAQ2_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates
  QAlgorithms QAlgorithms.Complexity GL2QFT_TotalAQ2_Aux in
theorem solution :
    UniformlyImplementsOn (fun D => D.q = 2) (fun D => inCodeA D) (fun D => outCodeA D)
      (fun D => totalA D) := by
  have hU0_all : UniformlyImplementsOn (fun _ => True) (fun _ (x : Qubits 1) => x)
      (fun _ (y : Qubits 1) => y) U_q :=
    sk_uniform_u2 U_q (fun D _ => U_q_unitary D) U_q_approx
  have hU0 : UniformlyImplementsOn (fun D => D.q = 2) (fun _ (x : Qubits 1) => x)
      (fun _ (y : Qubits 1) => y) U_q :=
    uniformlyImplementsOn_mono hU0_all (fun _ _ => trivial)
  have hZ := impl_matZ (fun D => D.q = 2)
  have hId := impl_const_id (fun D => D.q = 2)
  have hU1 : UniformlyImplementsOn (fun D => D.q = 2) (fun _ (x : Qubits 1) => x)
      (fun _ (y : Qubits 1) => y) (fun D => U_q D * matZ) :=
    uniformlyImplementsOn_seq hZ hU0 fun D _ ψ => norm_mulVec_le_of_iso matZ matZ_iso ψ
  have hB0 : UniformlyImplementsOn (fun D => D.q = 2) (fun _ => boolAppCode (fun q : Qubits 1 => q))
      (fun _ => boolAppCode (fun q : Qubits 1 => q)) (fun D => ctrlMat (U_q D) 1) :=
    uniformlyImplementsOn_branch hU0 hId
  have hB1 : UniformlyImplementsOn (fun D => D.q = 2) (fun _ => boolAppCode (fun q : Qubits 1 => q))
      (fun _ => boolAppCode (fun q : Qubits 1 => q)) (fun D => ctrlMat 1 (U_q D * matZ)) :=
    uniformlyImplementsOn_branch hId hU1
  have hCore : UniformlyImplementsOn (fun D => D.q = 2) (fun _ => midCode3) (fun _ => midCode3)
      (fun D => ctrlMat (ctrlMat (U_q D) 1) (ctrlMat 1 (U_q D * matZ))) :=
    uniformlyImplementsOn_branch hB0 hB1
  have hPre := pre20_impl
  have hPost := post18_impl
  have hStep12 : UniformlyImplementsOn (fun D => D.q = 2) (fun D => inCodeA D) (fun _ => midCode3)
      (fun D => ctrlMat (ctrlMat (U_q D) 1) (ctrlMat 1 (U_q D * matZ)) * permMat (preMap D)) :=
    uniformlyImplementsOn_seq hPre hCore fun D hq2 ψ =>
      norm_mulVec_le_of_iso (permMat (preMap D)) (permMat_iso (preMap D) (preMap_injective D hq2)) ψ
  have hStep123 : UniformlyImplementsOn (fun D => D.q = 2) (fun D => inCodeA D) (fun D => outCodeA D)
      (fun D => (if h : D.q = 2 then permMat (postMap D h) else 0) *
        (ctrlMat (ctrlMat (U_q D) 1) (ctrlMat 1 (U_q D * matZ)) * permMat (preMap D))) := by
    refine uniformlyImplementsOn_seq hStep12 hPost fun D hq2 ψ => ?_
    have hpre_iso : (permMat (preMap D)).conjTranspose * permMat (preMap D) = 1 :=
      permMat_iso (preMap D) (preMap_injective D hq2)
    have hM2_unit : ∀ (M : Matrix (Qubits 1) (Qubits 1) ℂ),
        M ∈ Matrix.unitaryGroup (Qubits 1) ℂ → M.conjTranspose * M = 1 := fun _ hM =>
      Matrix.mem_unitaryGroup_iff'.mp hM
    have hUZ_iso : (U_q D * matZ).conjTranspose * (U_q D * matZ) = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (U_q D).conjTranspose,
        hM2_unit (U_q D) (U_q_unitary D), Matrix.one_mul, matZ_iso]
    have hone_iso : (1 : Matrix (Qubits 1) (Qubits 1) ℂ).conjTranspose * 1 = 1 := by
      rw [Matrix.conjTranspose_one, Matrix.one_mul]
    have hcore_iso := ctrlMat_iso _ _
      (ctrlMat_iso _ _ (hM2_unit (U_q D) (U_q_unitary D)) hone_iso)
      (ctrlMat_iso _ _ hone_iso hUZ_iso)
    have hprod_iso :
        (ctrlMat (ctrlMat (U_q D) 1) (ctrlMat 1 (U_q D * matZ)) * permMat (preMap D)).conjTranspose *
          (ctrlMat (ctrlMat (U_q D) 1) (ctrlMat 1 (U_q D * matZ)) * permMat (preMap D)) = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (ctrlMat (ctrlMat (U_q D) 1) (ctrlMat 1 (U_q D * matZ))).conjTranspose,
        hcore_iso, Matrix.one_mul, hpre_iso]
    exact norm_mulVec_le_of_iso _ hprod_iso ψ
  refine uniformlyImplementsOn_eq hStep123 fun D hq2 => ?_
  rw [dif_pos hq2]
  exact coreMat_eq_totalA D hq2
