-- Prove2me | solution 1 for CliffordTApprox.Ancilla.controlled_preparation
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-14T03:05:30.854785+00:00
-- url     : https://prove2.me/submissions/747e4261-4ab5-4fb2-9135-5ed7027d1981

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P85
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

section PB_CtrlGadgets

open QAlgorithms CliffordTApprox.Ancilla

/-! ### Elementary constants and gate memberships -/

noncomputable def pb_cg_omega : ℂ := QAlgorithms.gateT true true

theorem pb_cg_omega_eq : pb_cg_omega = Complex.exp (Complex.I * Real.pi / 4) := rfl

theorem pb_cg_omega_pow_four : pb_cg_omega ^ 4 = -1 := by
  rw [pb_cg_omega_eq, ← Complex.exp_nat_mul]
  have h : ((4 : ℕ) : ℂ) * (Complex.I * Real.pi / 4) = Real.pi * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_pi_mul_I]

theorem pb_cg_omega_pow_eight : pb_cg_omega ^ 8 = 1 := by
  calc
    pb_cg_omega ^ 8 = (pb_cg_omega ^ 4) ^ 2 := by ring
    _ = (-1) ^ 2 := by rw [pb_cg_omega_pow_four]
    _ = 1 := by norm_num

theorem pb_cg_omega_pow_mod_eight (k : ℕ) : pb_cg_omega ^ k = pb_cg_omega ^ (k % 8) := by
  have h := Nat.div_add_mod k 8
  conv_lhs => rw [← h, pow_add, pow_mul, pb_cg_omega_pow_eight, one_pow, one_mul]

theorem pb_cg_omega_formula :
    pb_cg_omega = (1 + Complex.I) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  rw [pb_cg_omega_eq, show Complex.I * Real.pi / 4 = ↑(Real.pi / 4) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  push_cast
  field_simp [h2]
  rw [hsq]

theorem pb_cg_hadamard_mem : Gate.ofMatrix1 hadamard ∈ htcxGateSet := by
  simp [htcxGateSet]

theorem pb_cg_gateT_mem : Gate.ofMatrix1 gateT ∈ htcxGateSet := by
  simp [htcxGateSet]

theorem pb_cg_cnot_mem : Gate.ofMatrix2 cnot ∈ htcxGateSet := by
  simp [htcxGateSet]

def pb_cg_wire1 {n : ℕ} (q : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩

def pb_cg_wire2 {n : ℕ} (a b : Fin n) (hab : a ≠ b) : Fin 2 ↪ Fin n :=
  ⟨![a, b], fun i j h => by
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h hab
    · exact absurd h.symm hab
    · rfl⟩

noncomputable def pb_cg_app1 {S : Set Gate} {n : ℕ} (M : Matrix Bool Bool ℂ)
    (hm : Gate.ofMatrix1 M ∈ S) (q : Fin n) : GateApp S n :=
  ⟨Gate.ofMatrix1 M, hm, pb_cg_wire1 q⟩

def pb_cg_app2 {S : Set Gate} {n : ℕ} (M : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hm : Gate.ofMatrix2 M ∈ S) (a b : Fin n) (hab : a ≠ b) : GateApp S n :=
  ⟨Gate.ofMatrix2 M, hm, pb_cg_wire2 a b hab⟩

noncomputable def pb_cg_hGate {n : ℕ} (q : Fin n) : GateApp htcxGateSet n :=
  pb_cg_app1 hadamard pb_cg_hadamard_mem q

noncomputable def pb_cg_tGate {n : ℕ} (q : Fin n) : GateApp htcxGateSet n :=
  pb_cg_app1 gateT pb_cg_gateT_mem q

def pb_cg_cnotGate {n : ℕ} (a b : Fin n) (hab : a ≠ b) : GateApp htcxGateSet n :=
  pb_cg_app2 cnot pb_cg_cnot_mem a b hab

def pb_cg_sub1 (M : Matrix Bool Bool ℂ) : Matrix (Qubits 1) (Qubits 1) ℂ :=
  M.submatrix (fun b => b 0) (fun b => b 0)

def pb_cg_sub2 (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) : Matrix (Qubits 2) (Qubits 2) ℂ :=
  M.submatrix (fun b => (b 0, b 1)) (fun b => (b 0, b 1))

/-! ### Action, circuit composition, and embedOp algebra -/

theorem pb_cg_act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  ext i
  simp [act]

theorem pb_cg_act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext i
  simp [act, Matrix.mulVec_mulVec]

theorem pb_cg_unitary_nil {S : Set Gate} {n : ℕ} :
    Circuit.unitary ([] : Circuit S n) = 1 := rfl

theorem pb_cg_unitary_cons {S : Set Gate} {n : ℕ} (g : GateApp S n) (c : Circuit S n) :
    Circuit.unitary (g :: c) = Circuit.unitary c * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

theorem pb_cg_unitary_append {S : Set Gate} {n : ℕ} (c₁ c₂ : Circuit S n) :
    Circuit.unitary (c₁ ++ c₂) = Circuit.unitary c₂ * Circuit.unitary c₁ := by
  simp [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

theorem pb_cg_size_append {S : Set Gate} {n : ℕ} (c₁ c₂ : Circuit S n) :
    (c₁ ++ c₂).size = c₁.size + c₂.size := by
  simp [Circuit.size]

theorem pb_cg_unitary_replicate {S : Set Gate} {n : ℕ} (k : ℕ) (g : GateApp S n) :
    Circuit.unitary (List.replicate k g) = (embedOp g.gate.mat g.wires) ^ k := by
  induction k with
  | zero => simp [Circuit.unitary]
  | succ k ih =>
      rw [List.replicate_succ, pb_cg_unitary_cons, ih, pow_succ]

theorem pb_cg_embedOp_mul {m n : ℕ} (A B : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    have hsum : (∑ x : Qubits n,
        (if ∀ a : Fin n, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
          (if ∀ a : Fin n, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0)) =
        ∑ x : Qubits n,
          if ∀ a : Fin n, a ∉ Set.range w → y a = x a then
            A (y ∘ w) (x ∘ w) * B (x ∘ w) (z ∘ w) else 0 := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
      · have hxz : ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun a ha =>
          (hyx a ha).symm.trans (hyz a ha)
        rw [if_pos hyx, if_pos hxz, if_pos hyx]
      · rw [if_neg hyx, zero_mul, if_neg hyx]
    rw [hsum, ← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun x _ => x ∘ w)
      (fun _ _ => Finset.mem_univ _)
      (fun x₁ hx₁ x₂ hx₂ h => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        funext a
        by_cases ha : a ∈ Set.range w
        · rcases ha with ⟨b, rfl⟩
          exact congrFun h b
        · exact (hx₁ a ha).symm.trans (hx₂ a ha))
      (fun x' _ => by
        classical
        refine ⟨fun a => if h : ∃ b : Fin m, w b = a then x' (Classical.choose h) else y a, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro a ha
          have hnot : ¬ ∃ b : Fin m, w b = a := by simpa [Set.mem_range] using ha
          simp [hnot]
        · funext b
          have h : ∃ b' : Fin m, w b' = w b := ⟨b, rfl⟩
          simp only [Function.comp_apply, h, ↓reduceDIte]
          exact congrArg x' (w.injective (Classical.choose_spec h)))
      (fun _ _ => rfl)
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
    · have hxz : ¬ ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun hxz =>
        hyz (fun a ha => (hyx a ha).trans (hxz a ha))
      rw [if_neg hxz, mul_zero]
    · rw [if_neg hyx, zero_mul]

theorem pb_cg_embedOp_pow {m n : ℕ} (A : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) (k : ℕ) :
    (embedOp A w) ^ k = embedOp (A ^ k) w := by
  induction k with
  | zero => simp [embedOp_one]
  | succ k ih => rw [pow_succ, pow_succ, ih, ← pb_cg_embedOp_mul]

theorem pb_cg_embedOp_trans {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (u : Fin k ↪ Fin m) (w : Fin m ↪ Fin n) :
    embedOp (embedOp M u) w = embedOp M (u.trans w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  by_cases hR : ∀ a : Fin n, a ∉ Set.range (u.trans w) → y a = z a
  · rw [if_pos hR]
    have hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a := by
      intro a ha
      apply hR a
      rintro ⟨c, hc⟩
      exact ha ⟨u c, hc⟩
    have hu : ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b) := by
      intro b hb
      apply hR (w b)
      rintro ⟨c, hc⟩
      exact hb ⟨c, w.injective hc⟩
    rw [if_pos hw]
    change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
      then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = _
    rw [if_pos hu]
  · rw [if_neg hR]
    simp only [not_forall] at hR
    rcases hR with ⟨a, ha, hne⟩
    by_cases haw : a ∈ Set.range w
    · rcases haw with ⟨b, rfl⟩
      have hbu : b ∉ Set.range u := by
        rintro ⟨c, rfl⟩
        exact ha ⟨c, rfl⟩
      by_cases hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a
      · rw [if_pos hw]
        change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
          then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = 0
        rw [if_neg (fun hu => hne (hu b hbu))]
      · rw [if_neg hw]
    · rw [if_neg (fun hw => hne (hw a haw))]

theorem pb_cg_sub1_one : pb_cg_sub1 (1 : Matrix Bool Bool ℂ) = 1 := by
  ext y z
  simp only [pb_cg_sub1, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : y 0 = z 0
  · have hyz : y = z := by funext i; fin_cases i; exact h
    simp [hyz]
  · have hyz : y ≠ z := fun heq => h (congrFun heq 0)
    simp [h, hyz]

theorem pb_cg_sub1_mul (A B : Matrix Bool Bool ℂ) :
    pb_cg_sub1 (A * B) = pb_cg_sub1 A * pb_cg_sub1 B := by
  ext y z
  simp only [pb_cg_sub1, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) Bool).symm]
  simp [Equiv.funUnique]

theorem pb_cg_sub1_pow (A : Matrix Bool Bool ℂ) (k : ℕ) :
    (pb_cg_sub1 A) ^ k = pb_cg_sub1 (A ^ k) := by
  induction k with
  | zero => simp [pb_cg_sub1_one]
  | succ k ih => rw [pow_succ, pow_succ, ih, ← pb_cg_sub1_mul]

theorem pb_cg_sub2_one : pb_cg_sub2 (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 1 := by
  ext y z
  simp only [pb_cg_sub2, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : (y 0, y 1) = (z 0, z 1)
  · have hyz : y = z := by
      funext i; fin_cases i
      · exact (Prod.ext_iff.1 h).1
      · exact (Prod.ext_iff.1 h).2
    simp [hyz]
  · have hyz : y ≠ z := fun heq => h (by subst heq; rfl)
    simp [h, hyz]

theorem pb_cg_sub2_mul (A B : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    pb_cg_sub2 (A * B) = pb_cg_sub2 A * pb_cg_sub2 B := by
  ext y z
  simp only [pb_cg_sub2, Matrix.submatrix_apply, Matrix.mul_apply]
  let e : Qubits 2 ≃ Bool × Bool :=
    ⟨fun b => (b 0, b 1), fun p => ![p.1, p.2],
      fun b => by funext i; fin_cases i <;> rfl,
      fun p => by rcases p with ⟨a, b⟩; rfl⟩
  exact (Equiv.sum_comp e (fun p => A (y 0, y 1) p * B p (z 0, z 1))).symm

theorem pb_cg_cnot_mul_self : cnot * cnot = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  cases a <;> cases b <;> cases c <;> cases d <;> simp [cnot]

theorem pb_cg_gateT_pow_eight : gateT ^ 8 = 1 := by
  have h : gateT ^ 8 = Matrix.diagonal (fun x : Bool => (gateT x x) ^ 8) := by
    dsimp [gateT]
    rw [Matrix.diagonal_pow]
    ext a b
    cases a <;> cases b <;> simp
  rw [h]
  ext a b
  cases a <;> cases b <;> simp [gateT]
  rw [← pb_cg_omega_eq, pb_cg_omega_pow_eight]

/-! ### 1. Circuit inversion (`pb_cg_invCirc`) -/

noncomputable def pb_cg_invGate {n : ℕ} (g : GateApp htcxGateSet n) :
    Circuit htcxGateSet n :=
  open Classical in
  if g.gate = Gate.ofMatrix1 gateT then List.replicate 7 g else [g]

noncomputable def pb_cg_invCircN {n : ℕ} (c : Circuit htcxGateSet n) :
    Circuit htcxGateSet n :=
  c.reverse.flatMap pb_cg_invGate

noncomputable def pb_cg_invCirc (c : Circuit htcxGateSet (1 + 2)) :
    Circuit htcxGateSet (1 + 2) :=
  pb_cg_invCircN c

theorem pb_cg_invGate_size {n : ℕ} (g : GateApp htcxGateSet n) :
    (pb_cg_invGate g).size ≤ 7 := by
  classical
  dsimp only [pb_cg_invGate, Circuit.size]
  split_ifs <;> simp

theorem pb_cg_invCircN_size {n : ℕ} (c : Circuit htcxGateSet n) :
    (pb_cg_invCircN c).size ≤ 7 * c.size := by
  dsimp only [pb_cg_invCircN, Circuit.size]
  induction c with
  | nil => simp
  | cons g cs ih =>
      simp only [List.reverse_cons, List.flatMap_append, List.length_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.length_cons]
      have hg : (pb_cg_invGate g).length ≤ 7 := pb_cg_invGate_size g
      omega

theorem pb_cg_invCirc_size (c : Circuit htcxGateSet (1 + 2)) :
    (pb_cg_invCirc c).size ≤ 7 * c.size :=
  pb_cg_invCircN_size c

theorem pb_cg_hadamard_ne_gateT : Gate.ofMatrix1 hadamard ≠ Gate.ofMatrix1 gateT := by
  intro heq
  have h0 : (Gate.ofMatrix1 hadamard).mat (fun _ => false) (fun _ => false) =
      (Gate.ofMatrix1 gateT).mat (fun _ => false) (fun _ => false) :=
    congrArg (fun g : Gate => g.mat (fun _ => false) (fun _ => false)) heq
  simp only [Gate.ofMatrix1, Matrix.submatrix_apply, hadamard, Matrix.of_apply,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, gateT, Matrix.diagonal_apply] at h0
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) = 1 := by
    simpa using congrArg Inv.inv h0
  have hreal : Real.sqrt 2 = 1 := Complex.ofReal_injective hsq
  have h2 : (2 : ℝ) = 1 := by
    calc (2 : ℝ) = (Real.sqrt 2) ^ 2 := (Real.sq_sqrt (by norm_num)).symm
    _ = 1 ^ 2 := by rw [hreal]
    _ = 1 := one_pow 2
  norm_num at h2

theorem pb_cg_cnot_ne_gateT : Gate.ofMatrix2 cnot ≠ Gate.ofMatrix1 gateT := by
  intro heq
  have har := congrArg Gate.arity heq
  simp [Gate.ofMatrix1, Gate.ofMatrix2] at har

theorem pb_cg_embedOp_hadamard_mul_self {n : ℕ} (hw : Fin 1 ↪ Fin n) :
    embedOp (pb_cg_sub1 hadamard) hw * embedOp (pb_cg_sub1 hadamard) hw = 1 := by
  rw [← pb_cg_embedOp_mul, ← pb_cg_sub1_mul, hadamard_mul_self, pb_cg_sub1_one, embedOp_one]

theorem pb_cg_embedOp_gateT_pow_eight {n : ℕ} (hw : Fin 1 ↪ Fin n) :
    embedOp (pb_cg_sub1 gateT) hw ^ 8 = 1 := by
  rw [pb_cg_embedOp_pow, pb_cg_sub1_pow, pb_cg_gateT_pow_eight, pb_cg_sub1_one, embedOp_one]

theorem pb_cg_embedOp_cnot_mul_self {n : ℕ} (hw : Fin 2 ↪ Fin n) :
    embedOp (pb_cg_sub2 cnot) hw * embedOp (pb_cg_sub2 cnot) hw = 1 := by
  rw [← pb_cg_embedOp_mul, ← pb_cg_sub2_mul, pb_cg_cnot_mul_self, pb_cg_sub2_one, embedOp_one]

theorem pb_cg_invGate_mul {n : ℕ} (g : GateApp htcxGateSet n) :
    (pb_cg_invGate g).unitary * embedOp g.gate.mat g.wires = 1 := by
  classical
  rcases g with ⟨gt, hmem, hw⟩
  simp only [htcxGateSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · subst h
    simp only [pb_cg_invGate, if_neg pb_cg_hadamard_ne_gateT, pb_cg_unitary_cons, pb_cg_unitary_nil,
      one_mul]
    exact pb_cg_embedOp_hadamard_mul_self hw
  · subst h
    simp only [pb_cg_invGate, ↓reduceIte, pb_cg_unitary_replicate]
    rw [← pow_succ]
    exact pb_cg_embedOp_gateT_pow_eight hw
  · subst h
    simp only [pb_cg_invGate, if_neg pb_cg_cnot_ne_gateT, pb_cg_unitary_cons, pb_cg_unitary_nil,
      one_mul]
    exact pb_cg_embedOp_cnot_mul_self hw

theorem pb_cg_mul_invGate {n : ℕ} (g : GateApp htcxGateSet n) :
    embedOp g.gate.mat g.wires * (pb_cg_invGate g).unitary = 1 := by
  classical
  rcases g with ⟨gt, hmem, hw⟩
  simp only [htcxGateSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · subst h
    simp only [pb_cg_invGate, if_neg pb_cg_hadamard_ne_gateT, pb_cg_unitary_cons, pb_cg_unitary_nil,
      one_mul]
    exact pb_cg_embedOp_hadamard_mul_self hw
  · subst h
    simp only [pb_cg_invGate, ↓reduceIte, pb_cg_unitary_replicate]
    rw [← pow_succ']
    exact pb_cg_embedOp_gateT_pow_eight hw
  · subst h
    simp only [pb_cg_invGate, if_neg pb_cg_cnot_ne_gateT, pb_cg_unitary_cons, pb_cg_unitary_nil,
      one_mul]
    exact pb_cg_embedOp_cnot_mul_self hw

theorem pb_cg_invCircN_mul {n : ℕ} (c : Circuit htcxGateSet n) :
    (pb_cg_invCircN c).unitary * c.unitary = 1 := by
  induction c with
  | nil => simp [pb_cg_invCircN, pb_cg_unitary_nil]
  | cons g cs ih =>
      dsimp only [pb_cg_invCircN]
      simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, pb_cg_unitary_append, pb_cg_unitary_cons]
      change (pb_cg_invGate g).unitary * (pb_cg_invCircN cs).unitary *
          (Circuit.unitary cs * embedOp g.gate.mat g.wires) = 1
      calc
        (pb_cg_invGate g).unitary * (pb_cg_invCircN cs).unitary *
            (Circuit.unitary cs * embedOp g.gate.mat g.wires)
          = (pb_cg_invGate g).unitary * (((pb_cg_invCircN cs).unitary * Circuit.unitary cs) *
              embedOp g.gate.mat g.wires) := by simp only [Matrix.mul_assoc]
        _ = (pb_cg_invGate g).unitary * embedOp g.gate.mat g.wires := by rw [ih, one_mul]
        _ = 1 := pb_cg_invGate_mul g

theorem pb_cg_mul_invCircN {n : ℕ} (c : Circuit htcxGateSet n) :
    c.unitary * (pb_cg_invCircN c).unitary = 1 := by
  induction c with
  | nil => simp [pb_cg_invCircN, pb_cg_unitary_nil]
  | cons g cs ih =>
      dsimp only [pb_cg_invCircN]
      simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, pb_cg_unitary_append, pb_cg_unitary_cons]
      change Circuit.unitary cs * embedOp g.gate.mat g.wires *
          ((pb_cg_invGate g).unitary * (pb_cg_invCircN cs).unitary) = 1
      calc
        Circuit.unitary cs * embedOp g.gate.mat g.wires *
            ((pb_cg_invGate g).unitary * (pb_cg_invCircN cs).unitary)
          = Circuit.unitary cs * ((embedOp g.gate.mat g.wires * (pb_cg_invGate g).unitary) *
              (pb_cg_invCircN cs).unitary) := by simp only [Matrix.mul_assoc]
        _ = Circuit.unitary cs * (pb_cg_invCircN cs).unitary := by rw [pb_cg_mul_invGate g, one_mul]
        _ = 1 := ih

theorem pb_cg_invCirc_mul (c : Circuit htcxGateSet (1 + 2)) :
    (pb_cg_invCirc c).unitary * c.unitary = 1 :=
  pb_cg_invCircN_mul c

theorem pb_cg_mul_invCirc (c : Circuit htcxGateSet (1 + 2)) :
    c.unitary * (pb_cg_invCirc c).unitary = 1 :=
  pb_cg_mul_invCircN c

theorem pb_cg_fixes_false_append (c₁ c₂ : Circuit htcxGateSet (1 + 2))
    (h₁ : ∀ w : EuclideanSpace ℂ (Qubits 2),
      act c₁.unitary (dataTensor false w) = dataTensor false w)
    (h₂ : ∀ w : EuclideanSpace ℂ (Qubits 2),
      act c₂.unitary (dataTensor false w) = dataTensor false w)
    (w : EuclideanSpace ℂ (Qubits 2)) :
    act (c₁ ++ c₂).unitary (dataTensor false w) = dataTensor false w := by
  rw [pb_cg_unitary_append, pb_cg_act_mul, h₁, h₂]

theorem pb_cg_fixes_false_invCirc (c : Circuit htcxGateSet (1 + 2))
    (h : ∀ w : EuclideanSpace ℂ (Qubits 2),
      act c.unitary (dataTensor false w) = dataTensor false w)
    (w : EuclideanSpace ℂ (Qubits 2)) :
    act (pb_cg_invCirc c).unitary (dataTensor false w) = dataTensor false w := by
  calc
    act (pb_cg_invCirc c).unitary (dataTensor false w)
      = act (pb_cg_invCirc c).unitary (act c.unitary (dataTensor false w)) := by rw [h w]
    _ = act ((pb_cg_invCirc c).unitary * c.unitary) (dataTensor false w) :=
        (pb_cg_act_mul _ _ _).symm
    _ = dataTensor false w := by rw [pb_cg_invCirc_mul, pb_cg_act_one]

theorem pb_cg_preparesControlled_of_reduces (c : Circuit htcxGateSet (1 + 2))
    (v : EuclideanSpace ℂ (Qubits 2))
    (h0 : ∀ w : EuclideanSpace ℂ (Qubits 2),
      act c.unitary (dataTensor false w) = dataTensor false w)
    (h1 : act c.unitary (dataTensor true v) = dataTensor true (ket fun _ => false)) :
    PreparesControlled (pb_cg_invCirc c).unitary v := by
  refine ⟨pb_cg_fixes_false_invCirc c h0, ?_⟩
  calc
    act (pb_cg_invCirc c).unitary (dataTensor true (ket fun _ => false))
      = act (pb_cg_invCirc c).unitary (act c.unitary (dataTensor true v)) := by rw [h1]
    _ = act ((pb_cg_invCirc c).unitary * c.unitary) (dataTensor true v) :=
        (pb_cg_act_mul _ _ _).symm
    _ = dataTensor true v := by rw [pb_cg_invCirc_mul, pb_cg_act_one]

/-! ### 2. Controlled global `ω^m` phase (`pb_cg_ctrlOmegaPow`) -/

noncomputable def pb_cg_ctrlOmegaPow (m : Fin 8) : Circuit htcxGateSet (1 + 2) :=
  List.replicate m.val (pb_cg_tGate 0)

theorem pb_cg_ctrlOmegaPow_size (m : Fin 8) : (pb_cg_ctrlOmegaPow m).size ≤ 7 := by
  simp only [pb_cg_ctrlOmegaPow, Circuit.size, List.length_replicate]
  exact Nat.lt_succ_iff.mp m.isLt

theorem pb_cg_embedOp_app1 {S : Set Gate} {n : ℕ} (M : Matrix Bool Bool ℂ)
    (hm : Gate.ofMatrix1 M ∈ S) (q : Fin n) :
    embedOp (pb_cg_app1 M hm q).gate.mat (pb_cg_app1 M hm q).wires =
      Matrix.of fun y z => if ∀ a : Fin n, a ≠ q → y a = z a then M (y q) (z q) else 0 := by
  ext y z
  change (if ∀ a : Fin n, a ∉ Set.range (pb_cg_wire1 q) → y a = z a
    then M (y q) (z q) else 0) = _
  have hr : ∀ a : Fin n, (a ∉ Set.range (pb_cg_wire1 q)) ↔ a ≠ q := by
    intro a
    constructor
    · intro h heq; exact h ⟨0, heq.symm⟩
    · rintro h ⟨i, hi⟩; fin_cases i; exact h hi.symm
  simp only [hr, Matrix.of_apply]

theorem pb_cg_embedOp_tGate {n : ℕ} (q : Fin n) :
    embedOp (pb_cg_tGate q).gate.mat (pb_cg_tGate q).wires =
      Matrix.diagonal (fun x : Qubits n => pb_cg_omega ^ (if x q then 1 else 0)) := by
  rw [pb_cg_tGate, pb_cg_embedOp_app1]
  ext y z
  simp only [Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz
    simp only [ne_eq, implies_true, ↓reduceIte, gateT, Matrix.diagonal_apply]
    cases y q <;> simp [pb_cg_omega_eq]
  · rw [if_neg hyz]
    split_ifs with h1
    · simp only [gateT, Matrix.diagonal_apply]
      have hq : y q ≠ z q := by
        intro hq
        apply hyz
        funext a
        by_cases ha : a = q
        · subst ha; exact hq
        · exact h1 a ha
      exact if_neg hq
    · rfl

theorem pb_cg_ctrlOmegaPow_unitary (m : Fin 8) :
    (pb_cg_ctrlOmegaPow m).unitary =
      Matrix.diagonal (fun x : Qubits (1 + 2) => if x 0 then pb_cg_omega ^ m.val else 1) := by
  rw [pb_cg_ctrlOmegaPow, pb_cg_unitary_replicate, pb_cg_embedOp_tGate, Matrix.diagonal_pow]
  ext y z
  simp only [Matrix.diagonal_apply, Pi.pow_apply]
  split_ifs with hyz hy0
  · simp
  · simp
  · rfl

theorem pb_cg_ctrlOmegaPow_false (m : Fin 8) (w : EuclideanSpace ℂ (Qubits 2)) :
    act (pb_cg_ctrlOmegaPow m).unitary (dataTensor false w) = dataTensor false w := by
  rw [pb_cg_ctrlOmegaPow_unitary]
  ext z
  simp only [act, Matrix.mulVec_diagonal, dataTensor]
  change (if z 0 then pb_cg_omega ^ m.val else 1) *
      (if (qubitsAppendEquiv 1 2 z).1 0 = false then w (qubitsAppendEquiv 1 2 z).2 else 0) =
    if (qubitsAppendEquiv 1 2 z).1 0 = false then w (qubitsAppendEquiv 1 2 z).2 else 0
  have h0 : (qubitsAppendEquiv 1 2 z).1 0 = z 0 := rfl
  rw [h0]
  cases z 0 <;> simp

theorem pb_cg_ctrlOmegaPow_true (m : Fin 8) (u : EuclideanSpace ℂ (Qubits 2)) :
    act (pb_cg_ctrlOmegaPow m).unitary (dataTensor true u) =
      dataTensor true ((pb_cg_omega ^ m.val) • u) := by
  rw [pb_cg_ctrlOmegaPow_unitary]
  ext z
  simp only [act, Matrix.mulVec_diagonal, dataTensor]
  change (if z 0 then pb_cg_omega ^ m.val else 1) *
      (if (qubitsAppendEquiv 1 2 z).1 0 = true then u (qubitsAppendEquiv 1 2 z).2 else 0) =
    if (qubitsAppendEquiv 1 2 z).1 0 = true then
      ((pb_cg_omega ^ m.val) • u) (qubitsAppendEquiv 1 2 z).2 else 0
  have h0 : (qubitsAppendEquiv 1 2 z).1 0 = z 0 := rfl
  rw [h0]
  cases z 0 <;> simp

/-! ### 3. Permutation matrices, ancilla lifting, Toffoli, and `pb_cg_ctrlSwap` -/

def pb_cg_permMatrix {α : Type*} [DecidableEq α] (f : α → α) : Matrix α α ℂ :=
  Matrix.of fun y z => if y = f z then 1 else 0

theorem pb_cg_permMatrix_id {α : Type*} [DecidableEq α] :
    pb_cg_permMatrix (id : α → α) = 1 := by
  ext y z
  simp [pb_cg_permMatrix, Matrix.one_apply]

theorem pb_cg_permMatrix_mul {α : Type*} [Fintype α] [DecidableEq α] (f g : α → α) :
    pb_cg_permMatrix f * pb_cg_permMatrix g = pb_cg_permMatrix (f ∘ g) := by
  ext y z
  simp [pb_cg_permMatrix, Matrix.mul_apply]

theorem pb_cg_act_permMatrix_equiv {α : Type*} [Fintype α] [DecidableEq α]
    (e : α ≃ α) (u : EuclideanSpace ℂ α) :
    act (pb_cg_permMatrix e) u = WithLp.toLp 2 fun z => u (e.symm z) := by
  ext z
  simp only [act, pb_cg_permMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (e.symm z)]
  · simp
  · intro b _ hb
    have hne : z ≠ e b := fun h => hb (by rw [h, Equiv.symm_apply_apply])
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

def pb_cg_cnotFun {n : ℕ} (a t : Fin n) (x : Qubits n) : Qubits n :=
  fun k => if k = t then xor (x t) (x a) else x k

theorem pb_cg_cnotFun_invol {n : ℕ} (a t : Fin n) (hat : a ≠ t) (x : Qubits n) :
    pb_cg_cnotFun a t (pb_cg_cnotFun a t x) = x := by
  funext k
  by_cases hkt : k = t
  · subst hkt; simp [pb_cg_cnotFun, hat]
  · simp [pb_cg_cnotFun, hkt]

theorem pb_cg_embedOp_cnotGate {n : ℕ} (a t : Fin n) (hat : a ≠ t) :
    embedOp (pb_cg_cnotGate a t hat).gate.mat (pb_cg_cnotGate a t hat).wires =
      pb_cg_permMatrix (pb_cg_cnotFun a t) := by
  ext z x
  change (if ∀ k : Fin n, k ∉ Set.range ![a, t] → z k = x k
    then (if z a = x a ∧ z t = xor (x t) (x a) then (1 : ℂ) else 0) else 0) =
    if z = pb_cg_cnotFun a t x then 1 else 0
  have hc : (∀ k : Fin n, k ∉ Set.range ![a, t] → z k = x k) ∧
      (z a = x a ∧ z t = xor (x t) (x a)) ↔ z = pb_cg_cnotFun a t x := by
    constructor
    · rintro ⟨hk, ha, ht⟩
      funext k
      by_cases hkt : k = t
      · subst hkt; simp [pb_cg_cnotFun, ht]
      · by_cases hka : k = a
        · subst hka; simp [pb_cg_cnotFun, hat, ha]
        · have hnot : k ∉ Set.range ![a, t] := by
            rintro ⟨i, hi⟩
            fin_cases i
            · exact hka hi.symm
            · exact hkt hi.symm
          simp [pb_cg_cnotFun, hkt, hk k hnot]
    · intro hz
      subst hz
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        have hkt : k ≠ t := fun h => hk ⟨1, by simp [h]⟩
        simp [pb_cg_cnotFun, hkt]
      · simp [pb_cg_cnotFun, hat]
      · simp [pb_cg_cnotFun]
  by_cases h1 : ∀ k : Fin n, k ∉ Set.range ![a, t] → z k = x k
  · rw [if_pos h1]
    by_cases h2 : z a = x a ∧ z t = xor (x t) (x a)
    · rw [if_pos h2, if_pos (hc.1 ⟨h1, h2⟩)]
    · rw [if_neg h2, if_neg (fun h3 => h2 (hc.2 h3).2)]
  · rw [if_neg h1, if_neg (fun h3 => h1 (hc.2 h3).1)]

theorem pb_cg_diag_omega_pow {n : ℕ} (f : Qubits n → ℕ) (k : ℕ) :
    (Matrix.diagonal (fun x => pb_cg_omega ^ f x)) ^ k =
      Matrix.diagonal (fun x => pb_cg_omega ^ (k * f x)) := by
  rw [Matrix.diagonal_pow]
  congr 1
  funext x
  simp only [Pi.pow_apply, ← pow_mul, mul_comm]

theorem pb_cg_permMatrix_cnot_mul_diag_mul {n : ℕ} (a t : Fin n) (hat : a ≠ t)
    (d : Qubits n → ℂ) (X : Matrix (Qubits n) (Qubits n) ℂ) :
    pb_cg_permMatrix (pb_cg_cnotFun a t) * (Matrix.diagonal d * X) =
      Matrix.diagonal (fun x => d (pb_cg_cnotFun a t x)) *
        (pb_cg_permMatrix (pb_cg_cnotFun a t) * X) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  congr 1
  ext y z
  simp only [pb_cg_permMatrix, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply,
    mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hyz : y = pb_cg_cnotFun a t z <;> simp [hyz, pb_cg_cnotFun_invol a t hat z]

theorem pb_cg_diag_mul_diag_mul {α : Type*} [Fintype α] [DecidableEq α]
    (d₁ d₂ : α → ℂ) (X : Matrix α α ℂ) :
    Matrix.diagonal d₁ * (Matrix.diagonal d₂ * X) =
      Matrix.diagonal (fun x => d₁ x * d₂ x) * X := by
  rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]

theorem pb_cg_hadamard_pauliZ_hadamard : hadamard * pauliZ * hadamard = pauliX := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  ext a b
  cases a <;> cases b <;>
    simp [hadamard, pauliZ, pauliX, Matrix.mul_apply] <;>
    ring_nf <;> field_simp [hne] <;> simp [h2]

theorem pb_cg_embedOp_hGate_2 (y x : Qubits (1 + 2)) :
    embedOp (pb_cg_hGate (2 : Fin (1 + 2))).gate.mat
        (pb_cg_hGate (2 : Fin (1 + 2))).wires y x =
      if y 0 = x 0 ∧ y 1 = x 1 then hadamard (y 2) (x 2) else 0 := by
  rw [pb_cg_hGate, pb_cg_embedOp_app1, Matrix.of_apply]
  have hr : (∀ a : Fin (1 + 2), a ≠ 2 → y a = x a) ↔ (y 0 = x 0 ∧ y 1 = x 1) := by
    constructor
    · intro h; exact ⟨h 0 (by decide), h 1 (by decide)⟩
    · intro ⟨h0, h1⟩ a ha
      fin_cases a
      · exact h0
      · exact h1
      · exact absurd rfl ha
  simp only [hr]

theorem pb_cg_mul_diag_mul_apply {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Matrix α α ℂ) (d : α → ℂ) (y z : α) :
    (A * Matrix.diagonal d * B) y z = ∑ x : α, A y x * d x * B x z := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

def pb_cg_qubits3Equiv : Qubits (1 + 2) ≃ Bool × Bool × Bool where
  toFun x := (x 0, x 1, x 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

theorem pb_cg_sum_qubits3 (f : Qubits (1 + 2) → ℂ) :
    (∑ x : Qubits (1 + 2), f x) = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, f ![a, b, c] := by
  rw [← Equiv.sum_comp pb_cg_qubits3Equiv.symm]
  simp_rw [Fintype.sum_prod_type]
  rfl

noncomputable def pb_cg_midCirc : Circuit htcxGateSet (1 + 2) :=
  [pb_cg_tGate 0, pb_cg_tGate 1, pb_cg_tGate 2, pb_cg_cnotGate 0 1 (by decide)] ++
    List.replicate 7 (pb_cg_tGate 1) ++
    [pb_cg_cnotGate 2 1 (by decide), pb_cg_tGate 1, pb_cg_cnotGate 0 2 (by decide)] ++
    List.replicate 7 (pb_cg_tGate 2) ++
    [pb_cg_cnotGate 0 1 (by decide)] ++
    List.replicate 7 (pb_cg_tGate 1) ++
    [pb_cg_cnotGate 0 2 (by decide), pb_cg_cnotGate 2 1 (by decide)]

noncomputable def pb_cg_toffoliCirc : Circuit htcxGateSet (1 + 2) :=
  [pb_cg_hGate 2] ++ pb_cg_midCirc ++ [pb_cg_hGate 2]

theorem pb_cg_toffoliCirc_size : pb_cg_toffoliCirc.size = 33 := by
  simp [pb_cg_toffoliCirc, pb_cg_midCirc, Circuit.size]

def pb_cg_toffoliMat : Matrix (Qubits (1 + 2)) (Qubits (1 + 2)) ℂ :=
  Matrix.of fun y z =>
    if y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1) then 1 else 0

theorem pb_cg_midCirc_unitary :
    pb_cg_midCirc.unitary =
      Matrix.diagonal (fun x : Qubits (1 + 2) => if x 0 && x 1 && x 2 then (-1 : ℂ) else 1) := by
  have hunit : pb_cg_midCirc.unitary = pb_cg_midCirc.unitary * pb_cg_permMatrix id := by
    rw [pb_cg_permMatrix_id, Matrix.mul_one]
  rw [hunit, pb_cg_midCirc]
  simp only [pb_cg_unitary_append, pb_cg_unitary_cons, pb_cg_unitary_nil, pb_cg_unitary_replicate,
    one_mul]
  simp only [pb_cg_embedOp_tGate, pb_cg_diag_omega_pow, pb_cg_embedOp_cnotGate]
  simp only [Matrix.mul_assoc,
    pb_cg_permMatrix_cnot_mul_diag_mul (0 : Fin 3) 1 (by decide),
    pb_cg_permMatrix_cnot_mul_diag_mul (2 : Fin 3) 1 (by decide),
    pb_cg_permMatrix_cnot_mul_diag_mul (0 : Fin 3) 2 (by decide),
    pb_cg_diag_mul_diag_mul]
  simp only [pb_cg_permMatrix_mul]
  have hid : (pb_cg_cnotFun (2 : Fin 3) 1 ∘ pb_cg_cnotFun 0 2 ∘ pb_cg_cnotFun 0 1 ∘
      pb_cg_cnotFun 0 2 ∘ pb_cg_cnotFun 2 1 ∘ pb_cg_cnotFun 0 1 ∘ id :
      Qubits 3 → Qubits 3) = id := by
    funext x k
    fin_cases k <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      simp [pb_cg_cnotFun, h0, h1, h2]
  rw [hid, pb_cg_permMatrix_id, Matrix.mul_one]
  congr 1
  funext x
  simp only [← pow_add]
  rw [pb_cg_omega_pow_mod_eight,
    show (if (x 0 && x 1 && x 2) = true then (-1 : ℂ) else 1) =
      pb_cg_omega ^ (if x 0 && x 1 && x 2 then 4 else 0) by
        by_cases h0 : x 0 && x 1 && x 2 <;> simp [h0, pb_cg_omega_pow_four]]
  congr 1
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [pb_cg_cnotFun, h0, h1, h2]

theorem pb_cg_toffoliCirc_unitary : pb_cg_toffoliCirc.unitary = pb_cg_toffoliMat := by
  rw [pb_cg_toffoliCirc, pb_cg_unitary_append, pb_cg_unitary_append, pb_cg_unitary_cons,
    pb_cg_unitary_nil, one_mul, pb_cg_midCirc_unitary]
  ext y z
  rw [← Matrix.mul_assoc, pb_cg_mul_diag_mul_apply]
  simp only [pb_cg_embedOp_hGate_2]
  by_cases hyz : y 0 = z 0 ∧ y 1 = z 1
  · have hsum : (∑ x : Qubits (1 + 2),
        (if y 0 = x 0 ∧ y 1 = x 1 then hadamard (y 2) (x 2) else 0) *
          (if (x 0 && x 1 && x 2) = true then (-1 : ℂ) else 1) *
          (if x 0 = z 0 ∧ x 1 = z 1 then hadamard (x 2) (z 2) else 0)) =
        ∑ c : Bool, hadamard (y 2) c * (if z 0 && z 1 && c then (-1 : ℂ) else 1) *
          hadamard c (z 2) := by
      rw [pb_cg_sum_qubits3]
      rw [Fintype.sum_eq_single (z 0) (fun a ha => by simp [hyz.1, ha.symm])]
      rw [Fintype.sum_eq_single (z 1) (fun b hb => by simp [hyz.2, hb.symm])]
      simp [hyz.1, hyz.2]
    rw [hsum]
    by_cases h01 : z 0 = true ∧ z 1 = true
    · simp only [h01.1, h01.2, Bool.true_and]
      have hzh : ∑ c : Bool, hadamard (y 2) c * (if c = true then (-1 : ℂ) else 1) *
          hadamard c (z 2) = (hadamard * pauliZ * hadamard) (y 2) (z 2) := by
        simp [Matrix.mul_apply, pauliZ]
      rw [hzh, pb_cg_hadamard_pauliZ_hadamard]
      cases hy2 : y 2 <;> cases hz2 : z 2 <;>
        simp [pauliX, pb_cg_toffoliMat, hyz.1, hyz.2, h01.1, h01.2, hy2, hz2]
    · have hfalse : (z 0 && z 1) = false := by
        cases h0 : z 0 <;> cases h1 : z 1 <;> simp_all
      simp only [hfalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte, mul_one]
      have hh : ∑ c : Bool, hadamard (y 2) c * hadamard c (z 2) =
          (hadamard * hadamard) (y 2) (z 2) := rfl
      rw [hh, hadamard_mul_self, Matrix.one_apply]
      simp [pb_cg_toffoliMat, hyz.1, hyz.2, hfalse]
  · have hzero : (∑ x : Qubits (1 + 2),
        (if y 0 = x 0 ∧ y 1 = x 1 then hadamard (y 2) (x 2) else 0) *
          (if (x 0 && x 1 && x 2) = true then (-1 : ℂ) else 1) *
          (if x 0 = z 0 ∧ x 1 = z 1 then hadamard (x 2) (z 2) else 0)) = 0 := by
      refine Finset.sum_eq_zero (fun x _ => ?_)
      by_cases h1 : y 0 = x 0 ∧ y 1 = x 1
      · have h2 : ¬ (x 0 = z 0 ∧ x 1 = z 1) := fun h2 =>
          hyz ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
        rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul, zero_mul]
    rw [hzero]
    simp only [pb_cg_toffoliMat, Matrix.of_apply]
    rw [if_neg (fun h => hyz ⟨h.1, h.2.1⟩)]

/-! ### Ancilla lifting (`pb_cg_liftAnc`) and 2-qubit permutation circuits -/

def pb_cg_ancEmb : Fin 2 ↪ Fin (1 + 2) :=
  ⟨Fin.natAdd 1, Fin.natAdd_injective 2 1⟩

def pb_cg_liftAnc (c : Circuit htcxGateSet 2) : Circuit htcxGateSet (1 + 2) :=
  c.map fun g => ⟨g.gate, g.mem, g.wires.trans pb_cg_ancEmb⟩

theorem pb_cg_liftAnc_size (c : Circuit htcxGateSet 2) :
    (pb_cg_liftAnc c).size = c.size := by
  simp [pb_cg_liftAnc, Circuit.size]

theorem pb_cg_liftAnc_unitary (c : Circuit htcxGateSet 2) :
    (pb_cg_liftAnc c).unitary = embedOp c.unitary pb_cg_ancEmb := by
  induction c with
  | nil => simp [pb_cg_liftAnc, pb_cg_unitary_nil, embedOp_one]
  | cons g cs ih =>
      dsimp only [pb_cg_liftAnc]
      rw [List.map_cons, pb_cg_unitary_cons]
      change (pb_cg_liftAnc cs).unitary * embedOp g.gate.mat (g.wires.trans pb_cg_ancEmb) = _
      rw [ih]
      have hgate : embedOp g.gate.mat (g.wires.trans pb_cg_ancEmb) =
          embedOp (embedOp g.gate.mat g.wires) pb_cg_ancEmb :=
        (pb_cg_embedOp_trans g.gate.mat g.wires pb_cg_ancEmb).symm
      rw [hgate, ← pb_cg_embedOp_mul, pb_cg_unitary_cons]

theorem pb_cg_not_mem_range_ancEmb (a : Fin (1 + 2)) :
    a ∉ Set.range pb_cg_ancEmb ↔ a = 0 := by
  constructor
  · intro h
    fin_cases a
    · rfl
    · exact absurd ⟨0, rfl⟩ h
    · exact absurd ⟨1, rfl⟩ h
  · rintro rfl ⟨i, hi⟩
    fin_cases i <;> simp [pb_cg_ancEmb] at hi

theorem pb_cg_act_embedOp_ancEmb (M : Matrix (Qubits 2) (Qubits 2) ℂ)
    (x : Bool) (u : EuclideanSpace ℂ (Qubits 2)) :
    act (embedOp M pb_cg_ancEmb) (dataTensor x u) = dataTensor x (act M u) := by
  ext y
  simp only [act, Matrix.mulVec, dotProduct, dataTensor, embedOp, Matrix.of_apply]
  have h0 : ∀ z : Qubits (1 + 2), (qubitsAppendEquiv 1 2 z).1 0 = z 0 := fun _ => rfl
  simp_rw [h0]
  have hnot : ∀ z : Qubits (1 + 2),
      (∀ a : Fin (1 + 2), a ∉ Set.range pb_cg_ancEmb → y a = z a) ↔ y 0 = z 0 := by
    intro z
    constructor
    · intro h; exact h 0 ((pb_cg_not_mem_range_ancEmb 0).2 rfl)
    · intro h a ha; rw [(pb_cg_not_mem_range_ancEmb a).1 ha]; exact h
  simp_rw [hnot]
  rw [pb_cg_sum_qubits3]
  rw [Fintype.sum_eq_single (y 0) (fun a ha => by
    refine Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun c _ => ?_))
    simp [ha.symm])]
  by_cases hyx : y 0 = x
  · simp only [hyx, ↓reduceIte]
    have hcomp : ∀ b c : Bool,
        ((![x, b, c] : Qubits 3) ∘ pb_cg_ancEmb) = ![b, c] := by
      intro b c; funext i; fin_cases i <;> rfl
    have hcomp2 : ∀ b c : Bool,
        (qubitsAppendEquiv 1 2 ![x, b, c]).2 = ![b, c] := by
      intro b c; funext i; fin_cases i <;> rfl
    have heq : (∑ b : Bool, ∑ c : Bool,
        M (y ∘ pb_cg_ancEmb) (![x, b, c] ∘ pb_cg_ancEmb) *
          u (qubitsAppendEquiv 1 2 ![x, b, c]).2) =
        ∑ z : Qubits 2, M (qubitsAppendEquiv 1 2 y).2 z * u z := by
      have hy2 : y ∘ pb_cg_ancEmb = (qubitsAppendEquiv 1 2 y).2 := rfl
      rw [hy2]
      let e2 : Qubits 2 ≃ Bool × Bool :=
        ⟨fun z => (z 0, z 1), fun p => ![p.1, p.2],
          fun z => by funext i; fin_cases i <;> rfl,
          fun p => by rcases p with ⟨b, c⟩; rfl⟩
      rw [← Equiv.sum_comp e2.symm, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_))
      rw [hcomp, hcomp2]
      rfl
    simpa [hyx] using heq
  · simp [hyx]

theorem pb_cg_conj_anc_false (c_anc c_anc_inv : Circuit htcxGateSet 2)
    (hinv : c_anc_inv.unitary * c_anc.unitary = 1)
    (c : Circuit htcxGateSet (1 + 2))
    (hc : ∀ w : EuclideanSpace ℂ (Qubits 2),
      act c.unitary (dataTensor false w) = dataTensor false w)
    (w : EuclideanSpace ℂ (Qubits 2)) :
    act (pb_cg_liftAnc c_anc ++ c ++ pb_cg_liftAnc c_anc_inv).unitary (dataTensor false w) =
      dataTensor false w := by
  rw [pb_cg_unitary_append, pb_cg_unitary_append, pb_cg_act_mul, pb_cg_act_mul]
  rw [pb_cg_liftAnc_unitary, pb_cg_liftAnc_unitary]
  rw [pb_cg_act_embedOp_ancEmb, hc, pb_cg_act_embedOp_ancEmb, ← pb_cg_act_mul, hinv, pb_cg_act_one]

theorem pb_cg_conj_anc_true (c_anc c_anc_inv : Circuit htcxGateSet 2)
    (c : Circuit htcxGateSet (1 + 2))
    (M : Matrix (Qubits 2) (Qubits 2) ℂ)
    (hc : ∀ w : EuclideanSpace ℂ (Qubits 2),
      act c.unitary (dataTensor true w) = dataTensor true (act M w))
    (u : EuclideanSpace ℂ (Qubits 2)) :
    act (pb_cg_liftAnc c_anc ++ c ++ pb_cg_liftAnc c_anc_inv).unitary (dataTensor true u) =
      dataTensor true (act (c_anc_inv.unitary * M * c_anc.unitary) u) := by
  rw [pb_cg_unitary_append, pb_cg_unitary_append, pb_cg_act_mul, pb_cg_act_mul]
  rw [pb_cg_liftAnc_unitary, pb_cg_liftAnc_unitary]
  rw [pb_cg_act_embedOp_ancEmb, hc, pb_cg_act_embedOp_ancEmb]
  rw [← pb_cg_act_mul, ← pb_cg_act_mul, Matrix.mul_assoc]

/-! ### 2-qubit X gate, CNOT, and permutation circuit -/

noncomputable def pb_cg_xGate2 (q : Fin 2) : Circuit htcxGateSet 2 :=
  [pb_cg_hGate q] ++ List.replicate 4 (pb_cg_tGate q) ++ [pb_cg_hGate q]

def pb_cg_flipBit (q : Fin 2) (x : Qubits 2) : Qubits 2 :=
  fun k => if k = q then !(x q) else x k

theorem pb_cg_flipBit_invol (q : Fin 2) (x : Qubits 2) :
    pb_cg_flipBit q (pb_cg_flipBit q x) = x := by
  funext k
  by_cases h : k = q
  · subst h; simp [pb_cg_flipBit]
  · simp [pb_cg_flipBit, h]

theorem pb_cg_xGate2_size (q : Fin 2) : (pb_cg_xGate2 q).size = 6 := by
  simp [pb_cg_xGate2, Circuit.size]

theorem pb_cg_xGate2_reverse (q : Fin 2) : (pb_cg_xGate2 q).reverse = pb_cg_xGate2 q := by
  simp [pb_cg_xGate2, List.replicate_succ]

theorem pb_cg_gateT_pow_four : gateT ^ 4 = pauliZ := by
  have h : gateT ^ 4 = Matrix.diagonal (fun x : Bool => (gateT x x) ^ 4) := by
    dsimp [gateT]
    rw [Matrix.diagonal_pow]
    ext a b
    cases a <;> cases b <;> simp
  rw [h]
  ext a b
  cases a <;> cases b <;> simp [gateT, pauliZ]
  rw [← pb_cg_omega_eq, pb_cg_omega_pow_four]

theorem pb_cg_embedOp_hGate {n : ℕ} (q : Fin n) :
    embedOp (pb_cg_hGate q).gate.mat (pb_cg_hGate q).wires =
      embedOp (pb_cg_sub1 hadamard) (pb_cg_wire1 q) := rfl

theorem pb_cg_embedOp_tGate_sub1 {n : ℕ} (q : Fin n) :
    embedOp (pb_cg_tGate q).gate.mat (pb_cg_tGate q).wires =
      embedOp (pb_cg_sub1 gateT) (pb_cg_wire1 q) := rfl

theorem pb_cg_embedOp_sub1 {n : ℕ} (M : Matrix Bool Bool ℂ) (q : Fin n) :
    embedOp (pb_cg_sub1 M) (pb_cg_wire1 q) =
      Matrix.of fun y z => if ∀ a : Fin n, a ≠ q → y a = z a then M (y q) (z q) else 0 := by
  ext y z
  have hr : ∀ a : Fin n, (a ∉ Set.range (pb_cg_wire1 q)) ↔ a ≠ q := by
    intro a
    constructor
    · intro h heq; exact h ⟨0, heq.symm⟩
    · rintro h ⟨i, hi⟩; fin_cases i; exact h hi.symm
  simp only [embedOp, Matrix.of_apply, pb_cg_sub1, Matrix.submatrix_apply, Function.comp_apply,
    pb_cg_wire1]
  change (if ∀ a : Fin n, a ∉ Set.range (pb_cg_wire1 q) → y a = z a then M (y q) (z q) else 0) = _
  simp_rw [hr]

theorem pb_cg_xGate2_unitary (q : Fin 2) :
    (pb_cg_xGate2 q).unitary = pb_cg_permMatrix (pb_cg_flipBit q) := by
  rw [pb_cg_xGate2, pb_cg_unitary_append, pb_cg_unitary_append, pb_cg_unitary_cons,
    pb_cg_unitary_nil, one_mul, pb_cg_unitary_replicate]
  rw [pb_cg_embedOp_hGate, pb_cg_embedOp_tGate_sub1, pb_cg_embedOp_pow, ← Matrix.mul_assoc,
    ← pb_cg_embedOp_mul, ← pb_cg_embedOp_mul, pb_cg_sub1_pow, pb_cg_gateT_pow_four,
    ← pb_cg_sub1_mul, ← pb_cg_sub1_mul, pb_cg_hadamard_pauliZ_hadamard, pb_cg_embedOp_sub1]
  ext y z
  simp only [Matrix.of_apply, pb_cg_permMatrix]
  have hiff : ((∀ a : Fin 2, a ≠ q → y a = z a) ∧ y q = !(z q)) ↔ y = pb_cg_flipBit q z := by
    constructor
    · rintro ⟨ha, hq⟩
      funext a
      by_cases haq : a = q
      · subst haq; simp [pb_cg_flipBit, hq]
      · simp [pb_cg_flipBit, haq, ha a haq]
    · intro hy
      subst hy
      refine ⟨fun a ha => ?_, ?_⟩
      · simp [pb_cg_flipBit, ha]
      · simp [pb_cg_flipBit]
  by_cases h1 : ∀ a : Fin 2, a ≠ q → y a = z a
  · rw [if_pos h1]
    cases hyq : y q <;> cases hzq : z q <;> simp [pauliX]
    · intro h; rw [← hiff] at h; simp [hyq, hzq] at h
    · exact hiff.1 ⟨h1, by simp [hyq, hzq]⟩
    · exact hiff.1 ⟨h1, by simp [hyq, hzq]⟩
    · intro h; rw [← hiff] at h; simp [hyq, hzq] at h
  · rw [if_neg h1, if_neg (fun h => h1 (hiff.2 h).1)]

noncomputable def pb_cg_ancPermCirc (j l : Qubits 2) : Circuit htcxGateSet 2 :=
  let c1 : Circuit htcxGateSet 2 := if j 0 then [] else pb_cg_xGate2 0
  let c2 : Circuit htcxGateSet 2 := if j 1 then pb_cg_xGate2 1 else []
  let l' : Qubits 2 := ![xor (l 0) (!(j 0)), xor (l 1) (j 1)]
  let c3 : Circuit htcxGateSet 2 :=
    if l' = ![true, true] then []
    else if l' = ![false, true] then [pb_cg_cnotGate 1 0 (by decide)]
    else pb_cg_xGate2 0 ++ [pb_cg_cnotGate 0 1 (by decide)] ++ pb_cg_xGate2 0 ++
      [pb_cg_cnotGate 1 0 (by decide)]
  c1 ++ c2 ++ c3

theorem pb_cg_ancPermCirc_size (j l : Qubits 2) :
    (pb_cg_ancPermCirc j l).size ≤ 26 := by
  dsimp only [pb_cg_ancPermCirc]
  rw [pb_cg_size_append, pb_cg_size_append]
  have h1 : Circuit.size (if j 0 then ([] : Circuit htcxGateSet 2) else pb_cg_xGate2 0) ≤ 6 := by
    split_ifs <;> simp [Circuit.size, pb_cg_xGate2]
  have h2 : Circuit.size (if j 1 then pb_cg_xGate2 1 else ([] : Circuit htcxGateSet 2)) ≤ 6 := by
    split_ifs <;> simp [Circuit.size, pb_cg_xGate2]
  have h3 : Circuit.size (if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![true, true] then []
      else if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![false, true] then
        [pb_cg_cnotGate 1 0 (by decide)]
      else pb_cg_xGate2 0 ++ [pb_cg_cnotGate 0 1 (by decide)] ++ pb_cg_xGate2 0 ++
        [pb_cg_cnotGate 1 0 (by decide)]) ≤ 14 := by
    split_ifs <;> simp [Circuit.size, pb_cg_xGate2]
  omega

def pb_cg_ancPermFun (j l : Qubits 2) : Qubits 2 → Qubits 2 :=
  let f1 : Qubits 2 → Qubits 2 := if j 0 then id else pb_cg_flipBit 0
  let f2 : Qubits 2 → Qubits 2 := if j 1 then pb_cg_flipBit 1 else id
  let l' : Qubits 2 := ![xor (l 0) (!(j 0)), xor (l 1) (j 1)]
  let f3 : Qubits 2 → Qubits 2 :=
    if l' = ![true, true] then id
    else if l' = ![false, true] then pb_cg_cnotFun 1 0
    else pb_cg_cnotFun 1 0 ∘ pb_cg_flipBit 0 ∘ pb_cg_cnotFun 0 1 ∘ pb_cg_flipBit 0
  f3 ∘ f2 ∘ f1

def pb_cg_ancPermFunInv (j l : Qubits 2) : Qubits 2 → Qubits 2 :=
  let f1 : Qubits 2 → Qubits 2 := if j 0 then id else pb_cg_flipBit 0
  let f2 : Qubits 2 → Qubits 2 := if j 1 then pb_cg_flipBit 1 else id
  let l' : Qubits 2 := ![xor (l 0) (!(j 0)), xor (l 1) (j 1)]
  let f3inv : Qubits 2 → Qubits 2 :=
    if l' = ![true, true] then id
    else if l' = ![false, true] then pb_cg_cnotFun 1 0
    else pb_cg_flipBit 0 ∘ pb_cg_cnotFun 0 1 ∘ pb_cg_flipBit 0 ∘ pb_cg_cnotFun 1 0
  f1 ∘ f2 ∘ f3inv

theorem pb_cg_ancPermFun_leftInv (j l : Qubits 2) (x : Qubits 2) :
    pb_cg_ancPermFunInv j l (pb_cg_ancPermFun j l x) = x := by
  dsimp only [pb_cg_ancPermFun, pb_cg_ancPermFunInv, Function.comp_apply]
  have hf1 : ∀ y : Qubits 2,
      (if j 0 then id else pb_cg_flipBit 0) ((if j 0 then id else pb_cg_flipBit 0) y) = y := by
    intro y; split_ifs <;> simp [pb_cg_flipBit_invol]
  have hf2 : ∀ y : Qubits 2,
      (if j 1 then pb_cg_flipBit 1 else id) ((if j 1 then pb_cg_flipBit 1 else id) y) = y := by
    intro y; split_ifs <;> simp [pb_cg_flipBit_invol]
  have hf3 : ∀ y : Qubits 2,
      (if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![true, true] then id
        else if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![false, true] then
          pb_cg_cnotFun 1 0
        else pb_cg_flipBit 0 ∘ pb_cg_cnotFun 0 1 ∘ pb_cg_flipBit 0 ∘ pb_cg_cnotFun 1 0)
      ((if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![true, true] then id
        else if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![false, true] then
          pb_cg_cnotFun 1 0
        else pb_cg_cnotFun 1 0 ∘ pb_cg_flipBit 0 ∘ pb_cg_cnotFun 0 1 ∘ pb_cg_flipBit 0) y) = y := by
    intro y
    split_ifs <;> simp [pb_cg_cnotFun_invol, pb_cg_flipBit_invol]
  rw [hf3, hf2, hf1]

theorem pb_cg_ancPermFun_rightInv (j l : Qubits 2) (x : Qubits 2) :
    pb_cg_ancPermFun j l (pb_cg_ancPermFunInv j l x) = x := by
  dsimp only [pb_cg_ancPermFun, pb_cg_ancPermFunInv, Function.comp_apply]
  have hf1 : ∀ y : Qubits 2,
      (if j 0 then id else pb_cg_flipBit 0) ((if j 0 then id else pb_cg_flipBit 0) y) = y := by
    intro y; split_ifs <;> simp [pb_cg_flipBit_invol]
  have hf2 : ∀ y : Qubits 2,
      (if j 1 then pb_cg_flipBit 1 else id) ((if j 1 then pb_cg_flipBit 1 else id) y) = y := by
    intro y; split_ifs <;> simp [pb_cg_flipBit_invol]
  have hf3 : ∀ y : Qubits 2,
      (if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![true, true] then id
        else if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![false, true] then
          pb_cg_cnotFun 1 0
        else pb_cg_cnotFun 1 0 ∘ pb_cg_flipBit 0 ∘ pb_cg_cnotFun 0 1 ∘ pb_cg_flipBit 0)
      ((if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![true, true] then id
        else if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![false, true] then
          pb_cg_cnotFun 1 0
        else pb_cg_flipBit 0 ∘ pb_cg_cnotFun 0 1 ∘ pb_cg_flipBit 0 ∘ pb_cg_cnotFun 1 0) y) = y := by
    intro y
    split_ifs <;> simp [pb_cg_cnotFun_invol, pb_cg_flipBit_invol]
  rw [hf1, hf2, hf3]

def pb_cg_ancPermEquiv (j l : Qubits 2) : Qubits 2 ≃ Qubits 2 :=
  ⟨pb_cg_ancPermFun j l, pb_cg_ancPermFunInv j l,
    pb_cg_ancPermFun_leftInv j l, pb_cg_ancPermFun_rightInv j l⟩

theorem pb_cg_ancPermCirc_unitary (j l : Qubits 2) :
    (pb_cg_ancPermCirc j l).unitary = pb_cg_permMatrix (pb_cg_ancPermFun j l) := by
  dsimp only [pb_cg_ancPermCirc, pb_cg_ancPermFun]
  rw [pb_cg_unitary_append, pb_cg_unitary_append]
  have hu1 : Circuit.unitary (if j 0 then ([] : Circuit htcxGateSet 2) else pb_cg_xGate2 0) =
      pb_cg_permMatrix (if j 0 then id else pb_cg_flipBit 0) := by
    split_ifs
    · simp [pb_cg_unitary_nil, pb_cg_permMatrix_id]
    · exact pb_cg_xGate2_unitary 0
  have hu2 : Circuit.unitary (if j 1 then pb_cg_xGate2 1 else ([] : Circuit htcxGateSet 2)) =
      pb_cg_permMatrix (if j 1 then pb_cg_flipBit 1 else id) := by
    split_ifs
    · exact pb_cg_xGate2_unitary 1
    · simp [pb_cg_unitary_nil, pb_cg_permMatrix_id]
  have hu3 : Circuit.unitary (if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![true, true] then []
      else if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![false, true] then
        [pb_cg_cnotGate 1 0 (by decide)]
      else pb_cg_xGate2 0 ++ [pb_cg_cnotGate 0 1 (by decide)] ++ pb_cg_xGate2 0 ++
        [pb_cg_cnotGate 1 0 (by decide)]) =
      pb_cg_permMatrix
        (if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![true, true] then id
          else if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![false, true] then
            pb_cg_cnotFun 1 0
          else pb_cg_cnotFun 1 0 ∘ pb_cg_flipBit 0 ∘ pb_cg_cnotFun 0 1 ∘ pb_cg_flipBit 0) := by
    split_ifs
    · simp [pb_cg_unitary_nil, pb_cg_permMatrix_id]
    · simp [pb_cg_unitary_cons, pb_cg_unitary_nil, pb_cg_embedOp_cnotGate]
    · simp only [pb_cg_unitary_append, pb_cg_unitary_cons, pb_cg_unitary_nil, one_mul,
        pb_cg_xGate2_unitary, pb_cg_embedOp_cnotGate, pb_cg_permMatrix_mul]
  rw [hu1, hu2, hu3, pb_cg_permMatrix_mul, pb_cg_permMatrix_mul]

theorem pb_cg_ancPermCirc_reverse_unitary (j l : Qubits 2) :
    Circuit.unitary (pb_cg_ancPermCirc j l).reverse = pb_cg_permMatrix (pb_cg_ancPermFunInv j l) := by
  dsimp only [pb_cg_ancPermCirc, pb_cg_ancPermFunInv]
  simp only [List.reverse_append, pb_cg_unitary_append]
  have hu1 : Circuit.unitary (if j 0 then ([] : Circuit htcxGateSet 2) else pb_cg_xGate2 0).reverse =
      pb_cg_permMatrix (if j 0 then id else pb_cg_flipBit 0) := by
    split_ifs
    · simp [pb_cg_unitary_nil, pb_cg_permMatrix_id]
    · rw [pb_cg_xGate2_reverse]; exact pb_cg_xGate2_unitary 0
  have hu2 : Circuit.unitary (if j 1 then pb_cg_xGate2 1 else ([] : Circuit htcxGateSet 2)).reverse =
      pb_cg_permMatrix (if j 1 then pb_cg_flipBit 1 else id) := by
    split_ifs
    · rw [pb_cg_xGate2_reverse]; exact pb_cg_xGate2_unitary 1
    · simp [pb_cg_unitary_nil, pb_cg_permMatrix_id]
  have hu3 : Circuit.unitary (if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![true, true] then []
      else if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![false, true] then
        [pb_cg_cnotGate 1 0 (by decide)]
      else pb_cg_xGate2 0 ++ [pb_cg_cnotGate 0 1 (by decide)] ++ pb_cg_xGate2 0 ++
        [pb_cg_cnotGate 1 0 (by decide)]).reverse =
      pb_cg_permMatrix
        (if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![true, true] then id
          else if (![xor (l 0) (!(j 0)), xor (l 1) (j 1)] : Qubits 2) = ![false, true] then
            pb_cg_cnotFun 1 0
          else pb_cg_flipBit 0 ∘ pb_cg_cnotFun 0 1 ∘ pb_cg_flipBit 0 ∘ pb_cg_cnotFun 1 0) := by
    split_ifs
    · simp [pb_cg_unitary_nil, pb_cg_permMatrix_id]
    · simp [pb_cg_unitary_cons, pb_cg_unitary_nil, pb_cg_embedOp_cnotGate]
    · simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        pb_cg_unitary_append, pb_cg_unitary_cons, pb_cg_unitary_nil, one_mul,
        pb_cg_xGate2_reverse, pb_cg_xGate2_unitary, pb_cg_embedOp_cnotGate, pb_cg_permMatrix_mul,
        Function.comp_assoc]
  rw [hu1, hu2, hu3, pb_cg_permMatrix_mul, pb_cg_permMatrix_mul, Function.comp_assoc]

theorem pb_cg_ancPermCirc_reverse_mul (j l : Qubits 2) :
    Circuit.unitary (pb_cg_ancPermCirc j l).reverse * (pb_cg_ancPermCirc j l).unitary = 1 := by
  rw [pb_cg_ancPermCirc_reverse_unitary, pb_cg_ancPermCirc_unitary, pb_cg_permMatrix_mul]
  have hcomp : pb_cg_ancPermFunInv j l ∘ pb_cg_ancPermFun j l = id := by
    funext x; exact pb_cg_ancPermFun_leftInv j l x
  rw [hcomp, pb_cg_permMatrix_id]

theorem pb_cg_ancPermFun_maps (j l : Qubits 2) (hjl : j ≠ l) :
    pb_cg_ancPermFun j l j = ![true, false] ∧ pb_cg_ancPermFun j l l = ![true, true] := by
  have hj_eq : j = ![j 0, j 1] := by funext i; fin_cases i <;> rfl
  have hl_eq : l = ![l 0, l 1] := by funext i; fin_cases i <;> rfl
  rw [hj_eq, hl_eq] at hjl ⊢
  cases hj0 : j 0 <;> cases hj1 : j 1 <;> cases hl0 : l 0 <;> cases hl1 : l 1
  all_goals
    simp only [hj0, hj1, hl0, hl1] at hjl ⊢
    try exact absurd rfl hjl
  all_goals
    constructor <;> funext i <;> fin_cases i <;>
      simp [pb_cg_ancPermFun, pb_cg_flipBit, pb_cg_cnotFun]

/-! ### `pb_cg_ctrlSwap` -/

noncomputable def pb_cg_ctrlSwap (j l : Qubits 2) (_hjl : j ≠ l) :
    Circuit htcxGateSet (1 + 2) :=
  pb_cg_liftAnc (pb_cg_ancPermCirc j l) ++ pb_cg_toffoliCirc ++
    pb_cg_liftAnc (pb_cg_ancPermCirc j l).reverse

theorem pb_cg_ctrlSwap_size (j l : Qubits 2) (hjl : j ≠ l) :
    (pb_cg_ctrlSwap j l hjl).size ≤ 100 := by
  dsimp only [pb_cg_ctrlSwap]
  rw [pb_cg_size_append, pb_cg_size_append, pb_cg_liftAnc_size, pb_cg_liftAnc_size]
  dsimp only [Circuit.size]
  rw [List.length_reverse]
  have h1 : (pb_cg_ancPermCirc j l).size ≤ 26 := pb_cg_ancPermCirc_size j l
  have h2 : pb_cg_toffoliCirc.size = 33 := pb_cg_toffoliCirc_size
  dsimp only [Circuit.size] at h1 h2
  omega

theorem pb_cg_toffoli_false (w : EuclideanSpace ℂ (Qubits 2)) :
    act pb_cg_toffoliCirc.unitary (dataTensor false w) = dataTensor false w := by
  rw [pb_cg_toffoliCirc_unitary]
  ext y
  simp only [act, Matrix.mulVec, dotProduct, pb_cg_toffoliMat, Matrix.of_apply, dataTensor,
    ite_mul, one_mul, zero_mul]
  have hq0 : ∀ q : Qubits (1 + 2), (qubitsAppendEquiv 1 2 q).1 0 = q 0 := fun _ => rfl
  simp_rw [hq0]
  by_cases h : y 0 = false
  · rw [if_pos h]
    rw [Finset.sum_eq_single y]
    · simp [h]
    · intro z _ hz
      have hne : ¬(y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1)) := by
        rintro ⟨e0, e1, e2⟩
        apply hz
        funext i
        fin_cases i
        · exact e0.symm
        · exact e1.symm
        · have hz0 : z 0 = false := e0.symm.trans h
          simpa [hz0] using e2.symm
      simp [hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun z _ => ?_)
    by_cases hz : z 0 = false
    · have hne : ¬(y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1)) :=
        fun ⟨e0, _⟩ => h (e0.trans hz)
      rw [if_neg hne]
    · simp [hz]

theorem pb_cg_toffoli_true (w : EuclideanSpace ℂ (Qubits 2)) :
    act pb_cg_toffoliCirc.unitary (dataTensor true w) =
      dataTensor true (act (pb_cg_permMatrix (Equiv.swap (![true, false] : Qubits 2) ![true, true])) w) := by
  rw [pb_cg_toffoliCirc_unitary, pb_cg_act_permMatrix_equiv]
  ext y
  simp only [act, Matrix.mulVec, dotProduct, pb_cg_toffoliMat, Matrix.of_apply, dataTensor,
    ite_mul, one_mul, zero_mul]
  have hq0 : ∀ q : Qubits (1 + 2), (qubitsAppendEquiv 1 2 q).1 0 = q 0 := fun _ => rfl
  simp_rw [hq0]
  by_cases h : y 0 = true
  · rw [if_pos h]
    let y' : Qubits (1 + 2) := ![true, y 1, xor (y 2) (y 1)]
    have hy' : y' 0 = true := rfl
    have hy'2 : (qubitsAppendEquiv 1 2 y').2 =
        Equiv.swap (![true, false] : Qubits 2) ![true, true] (qubitsAppendEquiv 1 2 y).2 := by
      have hsub : (qubitsAppendEquiv 1 2 y).2 = ![y 1, y 2] := by
        funext i; fin_cases i <;> rfl
      have hsub' : (qubitsAppendEquiv 1 2 y').2 = ![y 1, xor (y 2) (y 1)] := by
        funext i; fin_cases i <;> rfl
      rw [hsub, hsub']
      funext i
      cases hy1 : y 1 <;> cases hy2 : y 2 <;>
        fin_cases i <;> simp [Equiv.swap_apply_def]
    rw [Finset.sum_eq_single y']
    · have hcond : y 0 = y' 0 ∧ y 1 = y' 1 ∧ y 2 = xor (y' 2) (y' 0 && y' 1) := by
        refine ⟨h, rfl, ?_⟩
        cases h1 : y 1 <;> cases h2 : y 2 <;> simp [y', h1, h2]
      rw [if_pos hcond, if_pos hy', hy'2, Equiv.symm_swap]
    · intro z _ hz
      have hne : ¬(y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1)) := by
        rintro ⟨e0, e1, e2⟩
        apply hz
        funext i
        fin_cases i
        · exact e0.symm.trans h
        · exact e1.symm
        · have hz0 : z 0 = true := e0.symm.trans h
          have hz1 : z 1 = y 1 := e1.symm
          rw [hz0, hz1, Bool.true_and] at e2
          dsimp [y']
          cases hy1 : y 1 <;> cases hz2 : z 2 <;> simp [hy1, hz2] at e2 ⊢ <;> exact e2
      simp [hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun z _ => ?_)
    by_cases hz : z 0 = true
    · have hne : ¬(y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1)) :=
        fun ⟨e0, _⟩ => h (e0.trans hz)
      simp [hne]
    · simp [hz]

theorem pb_cg_ctrlSwap_false (j l : Qubits 2) (hjl : j ≠ l)
    (w : EuclideanSpace ℂ (Qubits 2)) :
    act (pb_cg_ctrlSwap j l hjl).unitary (dataTensor false w) = dataTensor false w :=
  pb_cg_conj_anc_false (pb_cg_ancPermCirc j l) (pb_cg_ancPermCirc j l).reverse
    (pb_cg_ancPermCirc_reverse_mul j l) pb_cg_toffoliCirc pb_cg_toffoli_false w

theorem pb_cg_ctrlSwap_true (j l : Qubits 2) (hjl : j ≠ l)
    (u : EuclideanSpace ℂ (Qubits 2)) :
    act (pb_cg_ctrlSwap j l hjl).unitary (dataTensor true u) =
      dataTensor true (WithLp.toLp 2 fun z => u (Equiv.swap j l z)) := by
  dsimp only [pb_cg_ctrlSwap]
  rw [pb_cg_conj_anc_true _ _ _ _ pb_cg_toffoli_true u]
  rw [pb_cg_ancPermCirc_unitary, pb_cg_ancPermCirc_reverse_unitary]
  rw [pb_cg_permMatrix_mul, pb_cg_permMatrix_mul, Function.comp_assoc]
  have hmaps := pb_cg_ancPermFun_maps j l hjl
  have hcomp : pb_cg_ancPermFunInv j l ∘ (Equiv.swap (![true, false] : Qubits 2) ![true, true] ∘
      pb_cg_ancPermFun j l) = Equiv.swap j l := by
    funext z
    dsimp only [Function.comp_apply]
    by_cases hzj : z = j
    · subst hzj
      rw [hmaps.1, Equiv.swap_apply_left, ← hmaps.2, pb_cg_ancPermFun_leftInv, Equiv.swap_apply_left]
    · by_cases hzl : z = l
      · subst hzl
        rw [hmaps.2, Equiv.swap_apply_right, ← hmaps.1, pb_cg_ancPermFun_leftInv,
          Equiv.swap_apply_right]
      · have h1 : pb_cg_ancPermFun j l z ≠ ![true, false] := by
          intro h
          apply hzj
          calc z = pb_cg_ancPermFunInv j l (pb_cg_ancPermFun j l z) :=
              (pb_cg_ancPermFun_leftInv j l z).symm
            _ = pb_cg_ancPermFunInv j l (pb_cg_ancPermFun j l j) := by rw [h, hmaps.1]
            _ = j := pb_cg_ancPermFun_leftInv j l j
        have h2 : pb_cg_ancPermFun j l z ≠ ![true, true] := by
          intro h
          apply hzl
          calc z = pb_cg_ancPermFunInv j l (pb_cg_ancPermFun j l z) :=
              (pb_cg_ancPermFun_leftInv j l z).symm
            _ = pb_cg_ancPermFunInv j l (pb_cg_ancPermFun j l l) := by rw [h, hmaps.2]
            _ = l := pb_cg_ancPermFun_leftInv j l l
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, pb_cg_ancPermFun_leftInv,
          Equiv.swap_apply_of_ne_of_ne hzj hzl]
  rw [hcomp, pb_cg_act_permMatrix_equiv, Equiv.symm_swap]

/-! ### 4. Doubly-controlled Hadamard (`pb_cg_ccHCirc`) and `pb_cg_ctrlTwoLevel` -/

noncomputable def pb_cg_u1q : Matrix Bool Bool ℂ :=
  hadamard * phaseS * hadamard * gateT

noncomputable def pb_cg_u1qDag : Matrix Bool Bool ℂ :=
  gateT ^ 7 * hadamard * gateT ^ 6 * hadamard

theorem pb_cg_gateT_pow_two : gateT ^ 2 = phaseS := by
  have h : gateT ^ 2 = Matrix.diagonal (fun x : Bool => (gateT x x) ^ 2) := by
    dsimp [gateT]
    rw [Matrix.diagonal_pow]
    ext a b
    cases a <;> cases b <;> simp
  rw [h]
  ext a b
  cases a <;> cases b <;> simp [gateT, phaseS]
  rw [← pb_cg_omega_eq, pb_cg_omega_formula]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp [hne]
  rw [h2]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem pb_cg_gateT_pow_six : gateT ^ 6 = Matrix.diagonal (fun a => if a then -Complex.I else 1) := by
  have h : gateT ^ 6 = (gateT ^ 2) ^ 3 := by rw [← pow_mul]
  rw [h, pb_cg_gateT_pow_two]
  ext a b
  cases a <;> cases b <;> simp [phaseS, pow_three, Matrix.mul_apply]

theorem pb_cg_gateT_pow_seven :
    gateT ^ 7 = Matrix.diagonal (fun a => if a then (1 - Complex.I) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 1) := by
  have h : gateT ^ 7 = gateT ^ 6 * gateT := by rw [← pow_succ]
  rw [h, pb_cg_gateT_pow_six]
  ext a b
  cases a <;> cases b <;> simp [gateT, Matrix.mul_apply]
  rw [← pb_cg_omega_eq, pb_cg_omega_formula]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem pb_cg_u1q_mul_dag : pb_cg_u1q * pb_cg_u1qDag = 1 := by
  dsimp only [pb_cg_u1q, pb_cg_u1qDag]
  rw [← pb_cg_gateT_pow_two]
  have h17 : gateT * gateT ^ 7 = gateT ^ 8 := (pow_succ' gateT 7).symm
  have h26 : gateT ^ 2 * gateT ^ 6 = gateT ^ 8 := (pow_add gateT 2 6).symm
  calc
    hadamard * gateT ^ 2 * hadamard * gateT * (gateT ^ 7 * hadamard * gateT ^ 6 * hadamard)
      = hadamard * gateT ^ 2 * hadamard * (gateT * gateT ^ 7) * (hadamard * gateT ^ 6 * hadamard) := by
          simp only [Matrix.mul_assoc]
    _ = hadamard * gateT ^ 2 * (hadamard * hadamard) * gateT ^ 6 * hadamard := by
          rw [h17, pb_cg_gateT_pow_eight, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
    _ = hadamard * (gateT ^ 2 * gateT ^ 6) * hadamard := by
          rw [hadamard_mul_self, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
    _ = hadamard * hadamard := by rw [h26, pb_cg_gateT_pow_eight, Matrix.mul_one]
    _ = 1 := hadamard_mul_self

theorem pb_cg_u1q_conj_pauliX : pb_cg_u1q * pauliX * pb_cg_u1qDag = hadamard := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h4 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, h2]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  dsimp only [pb_cg_u1q, pb_cg_u1qDag]
  rw [pb_cg_gateT_pow_six, pb_cg_gateT_pow_seven]
  ext a b
  cases a <;> cases b <;>
    simp [hadamard, phaseS, gateT, pauliX, Matrix.mul_apply,
      ← pb_cg_omega_eq, pb_cg_omega_formula] <;>
    field_simp [hne] <;>
    rw [h4] <;>
    ring_nf <;>
    simp only [Complex.I_sq] <;>
    ring

noncomputable def pb_cg_u1qCirc : Circuit htcxGateSet (1 + 2) :=
  [pb_cg_tGate 2, pb_cg_hGate 2] ++ List.replicate 2 (pb_cg_tGate 2) ++ [pb_cg_hGate 2]

noncomputable def pb_cg_u1qDagCirc : Circuit htcxGateSet (1 + 2) :=
  [pb_cg_hGate 2] ++ List.replicate 6 (pb_cg_tGate 2) ++ [pb_cg_hGate 2] ++
    List.replicate 7 (pb_cg_tGate 2)

noncomputable def pb_cg_ccHCirc : Circuit htcxGateSet (1 + 2) :=
  pb_cg_u1qDagCirc ++ pb_cg_toffoliCirc ++ pb_cg_u1qCirc

theorem pb_cg_ccHCirc_size : pb_cg_ccHCirc.size = 53 := by
  have htof : pb_cg_toffoliCirc.length = 33 := pb_cg_toffoliCirc_size
  simp [pb_cg_ccHCirc, pb_cg_u1qDagCirc, pb_cg_u1qCirc, Circuit.size, htof]

theorem pb_cg_u1qCirc_unitary :
    pb_cg_u1qCirc.unitary =
      embedOp (pb_cg_sub1 pb_cg_u1q) (pb_cg_wire1 (2 : Fin (1 + 2))) := by
  rw [pb_cg_u1qCirc, pb_cg_unitary_append, pb_cg_unitary_append]
  simp only [pb_cg_unitary_cons, pb_cg_unitary_nil, one_mul, pb_cg_unitary_replicate]
  rw [pb_cg_embedOp_hGate, pb_cg_embedOp_tGate_sub1, pb_cg_embedOp_pow,
    ← pb_cg_embedOp_mul, ← pb_cg_embedOp_mul, ← pb_cg_embedOp_mul,
    pb_cg_sub1_pow, pb_cg_gateT_pow_two, ← pb_cg_sub1_mul, ← pb_cg_sub1_mul, ← pb_cg_sub1_mul]
  simp only [pb_cg_u1q, Matrix.mul_assoc]

theorem pb_cg_u1qDagCirc_unitary :
    pb_cg_u1qDagCirc.unitary =
      embedOp (pb_cg_sub1 pb_cg_u1qDag) (pb_cg_wire1 (2 : Fin (1 + 2))) := by
  rw [pb_cg_u1qDagCirc, pb_cg_unitary_append, pb_cg_unitary_append, pb_cg_unitary_append,
    pb_cg_unitary_cons, pb_cg_unitary_nil, one_mul, pb_cg_unitary_replicate, pb_cg_unitary_replicate]
  rw [pb_cg_embedOp_hGate, pb_cg_embedOp_tGate_sub1, pb_cg_embedOp_pow, pb_cg_embedOp_pow,
    ← pb_cg_embedOp_mul, ← pb_cg_embedOp_mul, ← pb_cg_embedOp_mul,
    pb_cg_sub1_pow, pb_cg_sub1_pow, ← pb_cg_sub1_mul, ← pb_cg_sub1_mul, ← pb_cg_sub1_mul]
  simp only [pb_cg_u1qDag, Matrix.mul_assoc]

theorem pb_cg_embedOp_wire1_2 (M : Matrix Bool Bool ℂ) (y x : Qubits (1 + 2)) :
    embedOp (pb_cg_sub1 M) (pb_cg_wire1 (2 : Fin (1 + 2))) y x =
      if y 0 = x 0 ∧ y 1 = x 1 then M (y 2) (x 2) else 0 := by
  have hr : ∀ a : Fin (1 + 2),
      (a ∉ Set.range (pb_cg_wire1 (2 : Fin (1 + 2)))) ↔ a ≠ 2 := by
    intro a
    constructor
    · intro h heq; exact h ⟨0, heq.symm⟩
    · rintro h ⟨i, hi⟩; fin_cases i; exact h hi.symm
  have hr2 : (∀ a : Fin (1 + 2), a ≠ 2 → y a = x a) ↔ (y 0 = x 0 ∧ y 1 = x 1) := by
    constructor
    · intro h; exact ⟨h 0 (by decide), h 1 (by decide)⟩
    · intro ⟨h0, h1⟩ a ha
      fin_cases a
      · exact h0
      · exact h1
      · exact absurd rfl ha
  simp only [embedOp, Matrix.of_apply, pb_cg_sub1, Matrix.submatrix_apply,
    Function.comp_apply, pb_cg_wire1]
  change (if ∀ a : Fin (1 + 2), a ∉ Set.range (pb_cg_wire1 (2 : Fin (1 + 2))) → y a = x a
      then M (y 2) (x 2) else 0) = _
  simp_rw [hr, hr2]

noncomputable def pb_cg_ccHMat : Matrix (Qubits (1 + 2)) (Qubits (1 + 2)) ℂ :=
  Matrix.of fun y z =>
    if y 0 = z 0 ∧ y 1 = z 1 then
      if z 0 && z 1 then hadamard (y 2) (z 2)
      else if y 2 = z 2 then 1 else 0
    else 0

theorem pb_cg_ccHCirc_unitary : pb_cg_ccHCirc.unitary = pb_cg_ccHMat := by
  rw [pb_cg_ccHCirc, pb_cg_unitary_append, pb_cg_unitary_append, pb_cg_u1qCirc_unitary,
    pb_cg_u1qDagCirc_unitary, pb_cg_toffoliCirc_unitary, ← Matrix.mul_assoc]
  ext y z
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, pb_cg_embedOp_wire1_2, pb_cg_toffoliMat, Matrix.of_apply]
  by_cases hyz : y 0 = z 0 ∧ y 1 = z 1
  · have hsum : (∑ x : Qubits (1 + 2),
        (∑ x' : Qubits (1 + 2),
          (if y 0 = x' 0 ∧ y 1 = x' 1 then pb_cg_u1q (y 2) (x' 2) else 0) *
            (if x' 0 = x 0 ∧ x' 1 = x 1 ∧ x' 2 = xor (x 2) (x 0 && x 1) then 1 else 0)) *
          (if x 0 = z 0 ∧ x 1 = z 1 then pb_cg_u1qDag (x 2) (z 2) else 0)) =
        ∑ c : Bool,
          (if z 0 && z 1 then
            (∑ c' : Bool, pb_cg_u1q (y 2) c' * pauliX c' c) * pb_cg_u1qDag c (z 2)
          else pb_cg_u1q (y 2) c * pb_cg_u1qDag c (z 2)) := by
      rw [pb_cg_sum_qubits3]
      rw [Fintype.sum_eq_single (z 0) (fun a ha => by
        refine Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun c _ => ?_))
        simp [ha])]
      rw [Fintype.sum_eq_single (z 1) (fun b hb => by
        refine Finset.sum_eq_zero (fun c _ => ?_)
        simp [hb])]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, and_self, ↓reduceIte]
      rw [pb_cg_sum_qubits3]
      rw [Fintype.sum_eq_single (z 0) (fun a ha => by
        refine Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun c' _ => ?_))
        simp [ha])]
      rw [Fintype.sum_eq_single (z 1) (fun b hb => by
        refine Finset.sum_eq_zero (fun c' _ => ?_)
        simp [hb])]
      by_cases h01 : z 0 && z 1
      · simp only [h01, ↓reduceIte]
        rw [Fintype.sum_eq_single (!c) (fun c' hc' => by
          have hne : c' ≠ xor c true := by cases c <;> cases c' <;> simp_all
          have hne' : ¬((![z 0, z 1, c'] : Qubits 3) 0 = z 0 ∧
              (![z 0, z 1, c'] : Qubits 3) 1 = z 1 ∧
              (![z 0, z 1, c'] : Qubits 3) 2 = xor c true) := fun h => hne h.2.2
          rw [if_neg hne', mul_zero])]
        rw [Fintype.sum_eq_single (!c) (fun c' hc' => by
          have : pauliX c' c = 0 := by cases c <;> cases c' <;> simp_all [pauliX]
          simp [this])]
        have hpx : pauliX (!c) c = 1 := by cases c <;> simp [pauliX]
        have hxor' : (!c) = xor c true := by cases c <;> decide
        simp [hyz.1, hyz.2, hpx, ← hxor']
      · simp only [h01, Bool.false_eq_true, ↓reduceIte]
        rw [Fintype.sum_eq_single c (fun c' hc' => by
          have hne : c' ≠ xor c false := by simpa using hc'
          have hne' : ¬((![z 0, z 1, c'] : Qubits 3) 0 = z 0 ∧
              (![z 0, z 1, c'] : Qubits 3) 1 = z 1 ∧
              (![z 0, z 1, c'] : Qubits 3) 2 = xor c false) := fun h => hne h.2.2
          rw [if_neg hne', mul_zero])]
        simp [hyz.1, hyz.2]
    rw [hsum]
    simp only [pb_cg_ccHMat, Matrix.of_apply, hyz.1, hyz.2, and_self, ↓reduceIte]
    by_cases h01 : z 0 && z 1
    · simp only [h01, ↓reduceIte]
      have hid : (∑ c : Bool, (∑ c' : Bool, pb_cg_u1q (y 2) c' * pauliX c' c) * pb_cg_u1qDag c (z 2)) =
          (pb_cg_u1q * pauliX * pb_cg_u1qDag) (y 2) (z 2) := by
        simp [Matrix.mul_apply]
      rw [hid, pb_cg_u1q_conj_pauliX]
    · simp only [h01, Bool.false_eq_true, ↓reduceIte]
      have hid : (∑ c : Bool, pb_cg_u1q (y 2) c * pb_cg_u1qDag c (z 2)) =
          (pb_cg_u1q * pb_cg_u1qDag) (y 2) (z 2) := rfl
      rw [hid, pb_cg_u1q_mul_dag, Matrix.one_apply]
  · have hzero : (∑ x : Qubits (1 + 2),
        (∑ x' : Qubits (1 + 2),
          (if y 0 = x' 0 ∧ y 1 = x' 1 then pb_cg_u1q (y 2) (x' 2) else 0) *
            (if x' 0 = x 0 ∧ x' 1 = x 1 ∧ x' 2 = xor (x 2) (x 0 && x 1) then 1 else 0)) *
          (if x 0 = z 0 ∧ x 1 = z 1 then pb_cg_u1qDag (x 2) (z 2) else 0)) = 0 := by
      refine Finset.sum_eq_zero (fun x _ => ?_)
      by_cases hxz : x 0 = z 0 ∧ x 1 = z 1
      · have hinner : (∑ x' : Qubits (1 + 2),
            (if y 0 = x' 0 ∧ y 1 = x' 1 then pb_cg_u1q (y 2) (x' 2) else 0) *
              (if x' 0 = x 0 ∧ x' 1 = x 1 ∧ x' 2 = xor (x 2) (x 0 && x 1) then 1 else 0)) = 0 := by
          refine Finset.sum_eq_zero (fun x' _ => ?_)
          by_cases hyx' : y 0 = x' 0 ∧ y 1 = x' 1
          · have hne : ¬(x' 0 = x 0 ∧ x' 1 = x 1 ∧ x' 2 = xor (x 2) (x 0 && x 1)) := by
              rintro ⟨e0, e1, _⟩
              exact hyz ⟨hyx'.1.trans (e0.trans hxz.1), hyx'.2.trans (e1.trans hxz.2)⟩
            simp [hne]
          · simp [hyx']
        rw [hinner, zero_mul]
      · simp [hxz]
    rw [hzero]
    simp [pb_cg_ccHMat, hyz]

noncomputable def pb_cg_coreTwoLevel (m : Fin 8) : Circuit htcxGateSet (1 + 2) :=
  List.replicate m.val (pb_cg_tGate 2) ++ pb_cg_ccHCirc ++
    List.replicate ((8 - m.val) % 8) (pb_cg_tGate 2)

theorem pb_cg_coreTwoLevel_size (m : Fin 8) :
    (pb_cg_coreTwoLevel m).size ≤ 67 := by
  dsimp only [pb_cg_coreTwoLevel]
  rw [pb_cg_size_append, pb_cg_size_append]
  simp only [Circuit.size, List.length_replicate]
  have hcc : pb_cg_ccHCirc.size = 53 := pb_cg_ccHCirc_size
  dsimp only [Circuit.size] at hcc
  have h1 : m.val ≤ 7 := Nat.lt_succ_iff.mp m.isLt
  have h2 : (8 - m.val) % 8 ≤ 7 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega))
  omega

theorem pb_cg_diag_mul_ccH_mul_diag (m : Fin 8) (a b : Qubits (1 + 2)) :
    (Matrix.diagonal (fun x : Qubits (1 + 2) => pb_cg_omega ^ ((8 - m.val) % 8 * if x 2 then 1 else 0)) *
      pb_cg_ccHMat *
      Matrix.diagonal (fun x : Qubits (1 + 2) => pb_cg_omega ^ (m.val * if x 2 then 1 else 0))) a b =
    if a 0 = b 0 ∧ a 1 = b 1 then
      if b 0 && b 1 then
        pb_cg_omega ^ ((8 - m.val) % 8 * if a 2 then 1 else 0) * hadamard (a 2) (b 2) *
          pb_cg_omega ^ (m.val * if b 2 then 1 else 0)
      else if a 2 = b 2 then 1 else 0
    else 0 := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Matrix.diagonal_apply, pb_cg_ccHMat, Matrix.of_apply]
  rw [Fintype.sum_eq_single b (fun x hx => by simp [hx])]
  rw [Fintype.sum_eq_single a (fun x hx => by simp [hx.symm])]
  simp only [↓reduceIte]
  by_cases hab : a 0 = b 0 ∧ a 1 = b 1
  · simp only [hab.1, hab.2, and_self, ↓reduceIte]
    by_cases hb : b 0 && b 1
    · simp [hb]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : a 2 = b 2
      · simp only [h2, ↓reduceIte, mul_one]
        rw [← pow_add, ← add_mul, pb_cg_omega_pow_mod_eight]
        have hmod : ((8 - m.val) % 8 + m.val) % 8 = 0 := by
          have hm := m.isLt
          cases hm0 : m.val with
          | zero => simp
          | succ k =>
              have hk : k < 7 := by omega
              rw [Nat.mod_eq_of_lt (by omega : 8 - (k + 1) < 8)]
              omega
        have hmod' : (((8 - m.val) % 8 + m.val) * (if b 2 then 1 else 0)) % 8 = 0 := by
          cases b 2 <;> simp [hmod]
        rw [hmod', pow_zero]
      · simp [h2]
  · simp [hab]

theorem pb_cg_coreTwoLevel_false (m : Fin 8) (w : EuclideanSpace ℂ (Qubits 2)) :
    act (pb_cg_coreTwoLevel m).unitary (dataTensor false w) = dataTensor false w := by
  rw [pb_cg_coreTwoLevel, pb_cg_unitary_append, pb_cg_unitary_append,
    pb_cg_unitary_replicate, pb_cg_unitary_replicate, pb_cg_ccHCirc_unitary]
  rw [pb_cg_embedOp_tGate, pb_cg_diag_omega_pow, pb_cg_diag_omega_pow, ← Matrix.mul_assoc]
  ext y
  simp only [act, Matrix.mulVec, dotProduct, dataTensor]
  simp_rw [pb_cg_diag_mul_ccH_mul_diag m]
  have hq0 : ∀ q : Qubits (1 + 2), (qubitsAppendEquiv 1 2 q).1 0 = q 0 := fun _ => rfl
  simp_rw [hq0]
  by_cases h : y 0 = false
  · rw [if_pos h]
    rw [Finset.sum_eq_single y]
    · simp [h]
    · intro z _ hz
      by_cases h01 : y 0 = z 0 ∧ y 1 = z 1
      · have hz0 : z 0 = false := h01.1.symm.trans h
        have hyz2 : y 2 ≠ z 2 := fun e2 => by
          apply hz; funext i; fin_cases i
          · exact h01.1.symm
          · exact h01.2.symm
          · exact e2.symm
        simp [h01.1, h01.2, hz0, hyz2]
      · simp [h01]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun z _ => ?_)
    by_cases hz : z 0 = false
    · have hne : ¬(y 0 = z 0 ∧ y 1 = z 1) := fun ⟨e0, _⟩ => h (e0.trans hz)
      simp [hne]
    · simp [hz]

noncomputable def pb_cg_coreTwoLevel2Mat (m : Fin 8) : Matrix (Qubits 2) (Qubits 2) ℂ :=
  Matrix.of fun y z =>
    if y 0 = z 0 then
      if z 0 then
        pb_cg_omega ^ ((8 - m.val) % 8 * if y 1 then 1 else 0) * hadamard (y 1) (z 1) *
          pb_cg_omega ^ (m.val * if z 1 then 1 else 0)
      else if y 1 = z 1 then 1 else 0
    else 0

theorem pb_cg_coreTwoLevel_true (m : Fin 8) (w : EuclideanSpace ℂ (Qubits 2)) :
    act (pb_cg_coreTwoLevel m).unitary (dataTensor true w) =
      dataTensor true (act (pb_cg_coreTwoLevel2Mat m) w) := by
  rw [pb_cg_coreTwoLevel, pb_cg_unitary_append, pb_cg_unitary_append,
    pb_cg_unitary_replicate, pb_cg_unitary_replicate, pb_cg_ccHCirc_unitary]
  rw [pb_cg_embedOp_tGate, pb_cg_diag_omega_pow, pb_cg_diag_omega_pow, ← Matrix.mul_assoc]
  ext y
  simp only [act, Matrix.mulVec, dotProduct, dataTensor]
  simp_rw [pb_cg_diag_mul_ccH_mul_diag m]
  have hq0 : ∀ q : Qubits (1 + 2), (qubitsAppendEquiv 1 2 q).1 0 = q 0 := fun _ => rfl
  simp_rw [hq0]
  by_cases hy : y 0 = true
  · rw [if_pos hy]
    rw [pb_cg_sum_qubits3]
    rw [Fintype.sum_eq_single true (fun a ha => by
      refine Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun c _ => ?_))
      simp [ha])]
    have hcomp : ∀ b c : Bool,
        (qubitsAppendEquiv 1 2 ![true, b, c]).2 = ![b, c] := by
      intro b c; funext i; fin_cases i <;> rfl
    let e2 : Qubits 2 ≃ Bool × Bool :=
      ⟨fun z => (z 0, z 1), fun p => ![p.1, p.2],
        fun z => by funext i; fin_cases i <;> rfl,
        fun p => by rcases p with ⟨b, c⟩; rfl⟩
    have hrhs : (∑ z : Qubits 2, pb_cg_coreTwoLevel2Mat m (qubitsAppendEquiv 1 2 y).2 z * w z) =
        ∑ b : Bool, ∑ c : Bool, pb_cg_coreTwoLevel2Mat m (qubitsAppendEquiv 1 2 y).2 ![b, c] * w ![b, c] := by
      rw [← Equiv.sum_comp e2.symm, Fintype.sum_prod_type]
      rfl
    rw [hrhs]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_))
    simp only [Matrix.cons_val_zero, ↓reduceIte, hcomp, pb_cg_coreTwoLevel2Mat, Matrix.of_apply, hy]
    have hy1 : (qubitsAppendEquiv 1 2 y).2 0 = y 1 := rfl
    have hy2 : (qubitsAppendEquiv 1 2 y).2 1 = y 2 := rfl
    rw [hy1, hy2]
    cases b <;> cases c <;> by_cases hy1' : y 1 <;> by_cases hy2' : y 2 <;> simp [hy1', hy2']
  · rw [if_neg hy]
    refine Finset.sum_eq_zero (fun z _ => ?_)
    by_cases hz : z 0 = true
    · have hne : ¬(y 0 = z 0 ∧ y 1 = z 1) := fun ⟨e0, _⟩ => hy (e0.trans hz)
      simp [hne]
    · simp [hz]

noncomputable def pb_cg_twoLevelTarget (m : Fin 8) (j l : Qubits 2)
    (u : EuclideanSpace ℂ (Qubits 2)) : EuclideanSpace ℂ (Qubits 2) :=
  WithLp.toLp 2 fun z =>
    if z = j then (u j + pb_cg_omega ^ m.val * u l) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
    else if z = l then
      pb_cg_omega ^ ((8 - m.val) % 8) *
        ((u j - pb_cg_omega ^ m.val * u l) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
    else u z

theorem pb_cg_twoLevelTarget_apply_left (m : Fin 8) (j l : Qubits 2)
    (u : EuclideanSpace ℂ (Qubits 2)) :
    pb_cg_twoLevelTarget m j l u j =
      (u j + pb_cg_omega ^ m.val * u l) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  simp [pb_cg_twoLevelTarget]

theorem pb_cg_twoLevelTarget_apply_right (m : Fin 8) (j l : Qubits 2) (hjl : j ≠ l)
    (u : EuclideanSpace ℂ (Qubits 2)) :
    pb_cg_twoLevelTarget m j l u l =
      pb_cg_omega ^ ((8 - m.val) % 8) *
        ((u j - pb_cg_omega ^ m.val * u l) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
  simp [pb_cg_twoLevelTarget, hjl.symm]

theorem pb_cg_twoLevelTarget_apply_other (m : Fin 8) (j l : Qubits 2)
    (u : EuclideanSpace ℂ (Qubits 2)) {z : Qubits 2} (hzj : z ≠ j) (hzl : z ≠ l) :
    pb_cg_twoLevelTarget m j l u z = u z := by
  simp [pb_cg_twoLevelTarget, hzj, hzl]

noncomputable def pb_cg_ctrlTwoLevel (m : Fin 8) (j l : Qubits 2) (_hjl : j ≠ l) :
    Circuit htcxGateSet (1 + 2) :=
  pb_cg_liftAnc (pb_cg_ancPermCirc j l) ++ pb_cg_coreTwoLevel m ++
    pb_cg_liftAnc (pb_cg_ancPermCirc j l).reverse

theorem pb_cg_ctrlTwoLevel_size (m : Fin 8) (j l : Qubits 2) (hjl : j ≠ l) :
    (pb_cg_ctrlTwoLevel m j l hjl).size ≤ 200 := by
  dsimp only [pb_cg_ctrlTwoLevel]
  rw [pb_cg_size_append, pb_cg_size_append, pb_cg_liftAnc_size, pb_cg_liftAnc_size]
  dsimp only [Circuit.size]
  rw [List.length_reverse]
  have h1 : (pb_cg_ancPermCirc j l).size ≤ 26 := pb_cg_ancPermCirc_size j l
  have h2 : (pb_cg_coreTwoLevel m).size ≤ 67 := pb_cg_coreTwoLevel_size m
  dsimp only [Circuit.size] at h1 h2
  omega

theorem pb_cg_ctrlTwoLevel_false (m : Fin 8) (j l : Qubits 2) (hjl : j ≠ l)
    (w : EuclideanSpace ℂ (Qubits 2)) :
    act (pb_cg_ctrlTwoLevel m j l hjl).unitary (dataTensor false w) = dataTensor false w :=
  pb_cg_conj_anc_false (pb_cg_ancPermCirc j l) (pb_cg_ancPermCirc j l).reverse
    (pb_cg_ancPermCirc_reverse_mul j l) (pb_cg_coreTwoLevel m) (pb_cg_coreTwoLevel_false m) w

theorem pb_cg_act_conj_perm (φ φ_inv : Qubits 2 → Qubits 2)
    (hL : ∀ x, φ_inv (φ x) = x) (hR : ∀ x, φ (φ_inv x) = x)
    (M : Matrix (Qubits 2) (Qubits 2) ℂ) (u : EuclideanSpace ℂ (Qubits 2)) (z : Qubits 2) :
    act (pb_cg_permMatrix φ_inv * M * pb_cg_permMatrix φ) u z =
      ∑ x : Qubits 2, M (φ z) (φ x) * u x := by
  simp only [act, Matrix.mulVec, dotProduct]
  have hmat : ∀ a b : Qubits 2,
      (pb_cg_permMatrix φ_inv * M * pb_cg_permMatrix φ) a b = M (φ a) (φ b) := by
    intro a b
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, pb_cg_permMatrix, Matrix.of_apply]
    rw [Fintype.sum_eq_single (φ b) (fun x hx => by simp [hx])]
    rw [Fintype.sum_eq_single (φ a)]
    · simp [hL a]
    · intro y hy
      have hne : a ≠ φ_inv y := fun h => hy (by rw [h, hR])
      simp [hne]
  simp_rw [hmat]

theorem pb_cg_ctrlTwoLevel_true (m : Fin 8) (j l : Qubits 2) (hjl : j ≠ l)
    (u : EuclideanSpace ℂ (Qubits 2)) :
    act (pb_cg_ctrlTwoLevel m j l hjl).unitary (dataTensor true u) =
      dataTensor true (pb_cg_twoLevelTarget m j l u) := by
  dsimp only [pb_cg_ctrlTwoLevel]
  rw [pb_cg_conj_anc_true _ _ _ _ (pb_cg_coreTwoLevel_true m) u]
  rw [pb_cg_ancPermCirc_unitary, pb_cg_ancPermCirc_reverse_unitary]
  congr 1
  ext z
  rw [pb_cg_act_conj_perm (pb_cg_ancPermFun j l) (pb_cg_ancPermFunInv j l)
    (pb_cg_ancPermFun_leftInv j l) (pb_cg_ancPermFun_rightInv j l)
    (pb_cg_coreTwoLevel2Mat m) u z]
  have hmaps := pb_cg_ancPermFun_maps j l hjl
  let e2 : Qubits 2 ≃ Qubits 2 := pb_cg_ancPermEquiv j l
  have hsum : (∑ x : Qubits 2, pb_cg_coreTwoLevel2Mat m (pb_cg_ancPermFun j l z)
      (pb_cg_ancPermFun j l x) * u x) =
      ∑ y : Qubits 2, pb_cg_coreTwoLevel2Mat m (pb_cg_ancPermFun j l z) y *
        u (pb_cg_ancPermFunInv j l y) := by
    rw [← Equiv.sum_comp e2.symm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    change pb_cg_coreTwoLevel2Mat m (pb_cg_ancPermFun j l z)
        (pb_cg_ancPermFun j l (pb_cg_ancPermFunInv j l y)) *
        u (pb_cg_ancPermFunInv j l y) = _
    rw [pb_cg_ancPermFun_rightInv]
  rw [hsum]
  by_cases hzj : z = j
  · rw [hzj, hmaps.1, pb_cg_twoLevelTarget_apply_left]
    have hsum2 : (∑ y : Qubits 2, pb_cg_coreTwoLevel2Mat m ![true, false] y *
          u (pb_cg_ancPermFunInv j l y)) =
        pb_cg_coreTwoLevel2Mat m ![true, false] ![true, false] *
          u (pb_cg_ancPermFunInv j l ![true, false]) +
        pb_cg_coreTwoLevel2Mat m ![true, false] ![true, true] *
          u (pb_cg_ancPermFunInv j l ![true, true]) := by
      let eB : Qubits 2 ≃ Bool × Bool :=
        ⟨fun y => (y 0, y 1), fun p => ![p.1, p.2],
          fun y => by funext i; fin_cases i <;> rfl,
          fun p => by rcases p with ⟨a, b⟩; rfl⟩
      rw [← Equiv.sum_comp eB.symm, Fintype.sum_prod_type]
      simp [pb_cg_coreTwoLevel2Mat, eB]
      ring
    rw [hsum2]
    have hj_inv : pb_cg_ancPermFunInv j l ![true, false] = j := by
      rw [← hmaps.1, pb_cg_ancPermFun_leftInv]
    have hl_inv : pb_cg_ancPermFunInv j l ![true, true] = l := by
      rw [← hmaps.2, pb_cg_ancPermFun_leftInv]
    rw [hj_inv, hl_inv]
    simp [pb_cg_coreTwoLevel2Mat, hadamard]
    ring
  · by_cases hzl : z = l
    · rw [hzl, hmaps.2, pb_cg_twoLevelTarget_apply_right m j l hjl]
      have hsum2 : (∑ y : Qubits 2, pb_cg_coreTwoLevel2Mat m ![true, true] y *
            u (pb_cg_ancPermFunInv j l y)) =
          pb_cg_coreTwoLevel2Mat m ![true, true] ![true, false] *
            u (pb_cg_ancPermFunInv j l ![true, false]) +
          pb_cg_coreTwoLevel2Mat m ![true, true] ![true, true] *
            u (pb_cg_ancPermFunInv j l ![true, true]) := by
        let eB : Qubits 2 ≃ Bool × Bool :=
          ⟨fun y => (y 0, y 1), fun p => ![p.1, p.2],
            fun y => by funext i; fin_cases i <;> rfl,
            fun p => by rcases p with ⟨a, b⟩; rfl⟩
        rw [← Equiv.sum_comp eB.symm, Fintype.sum_prod_type]
        simp [pb_cg_coreTwoLevel2Mat, eB]
        ring
      rw [hsum2]
      have hj_inv : pb_cg_ancPermFunInv j l ![true, false] = j := by
        rw [← hmaps.1, pb_cg_ancPermFun_leftInv]
      have hl_inv : pb_cg_ancPermFunInv j l ![true, true] = l := by
        rw [← hmaps.2, pb_cg_ancPermFun_leftInv]
      rw [hj_inv, hl_inv]
      simp [pb_cg_coreTwoLevel2Mat, hadamard]
      ring
    · rw [pb_cg_twoLevelTarget_apply_other m j l u hzj hzl]
      have h0 : (pb_cg_ancPermFun j l z) 0 = false := by
        have hz1 : pb_cg_ancPermFun j l z ≠ ![true, false] := by
          intro h; apply hzj
          calc z = pb_cg_ancPermFunInv j l (pb_cg_ancPermFun j l z) :=
              (pb_cg_ancPermFun_leftInv j l z).symm
            _ = pb_cg_ancPermFunInv j l ![true, false] := by rw [h]
            _ = j := by rw [← hmaps.1, pb_cg_ancPermFun_leftInv]
        have hz2 : pb_cg_ancPermFun j l z ≠ ![true, true] := by
          intro h; apply hzl
          calc z = pb_cg_ancPermFunInv j l (pb_cg_ancPermFun j l z) :=
              (pb_cg_ancPermFun_leftInv j l z).symm
            _ = pb_cg_ancPermFunInv j l ![true, true] := by rw [h]
            _ = l := by rw [← hmaps.2, pb_cg_ancPermFun_leftInv]
        have hpeq : pb_cg_ancPermFun j l z =
            ![(pb_cg_ancPermFun j l z) 0, (pb_cg_ancPermFun j l z) 1] := by
          funext i; fin_cases i <;> rfl
        rw [hpeq] at hz1 hz2
        cases h0v : (pb_cg_ancPermFun j l z) 0 <;> cases h1v : (pb_cg_ancPermFun j l z) 1 <;>
          simp_all
      rw [Finset.sum_eq_single (pb_cg_ancPermFun j l z)]
      · simp [pb_cg_coreTwoLevel2Mat, h0, pb_cg_ancPermFun_leftInv]
      · intro y _ hy
        have hne : pb_cg_coreTwoLevel2Mat m (pb_cg_ancPermFun j l z) y = 0 := by
          by_cases h0y : (pb_cg_ancPermFun j l z) 0 = y 0
          · have h1y : (pb_cg_ancPermFun j l z) 1 ≠ y 1 := by
              intro h1y
              apply hy
              funext i; fin_cases i
              · exact h0y.symm
              · exact h1y.symm
            simp [pb_cg_coreTwoLevel2Mat, h0, ← h0y, h1y]
          · simp [pb_cg_coreTwoLevel2Mat, h0y]
        simp [hne]
      · intro hm; exact absurd (Finset.mem_univ _) hm

end PB_CtrlGadgets

/-!
Unconditional proof of `CliffordTApprox.Ancilla.controlled_preparation`.
-/

open scoped BigOperators
open QAlgorithms
open CliffordTApprox.Ancilla
open QAlgorithms.Papers.Independent.Gap48.P10
  (InZomega Residue bits residue residueMultiply Reducible omegaCoordinatesValue omegaCoordinates)
open QAlgorithms.Papers.Independent.Intakethird100.P85
  (ScalarExponent VectorExponent kResidue residueConjugate residueNorm)

/-! ## Part 1: Finite `Residue` combinatorics (`Fin 4 → ZMod 2`) -/

private def pb_cp_bits (n : ℕ) : Residue := fun i => ((n / 2 ^ (3 - i.val)) % 2 : ℕ)

private lemma pb_cp_bits_eq (n : ℕ) : pb_cp_bits n = bits n := rfl

private def pb_cp_resMul (a b : Residue) : Residue :=
  fun l => ∑ i : Fin 4, ∑ j : Fin 4,
    if (i.val + j.val) % 4 = (l.val + 3) % 4 then a i * b j else 0

private lemma pb_cp_resMul_eq (a b : Residue) : pb_cp_resMul a b = residueMultiply a b := rfl

private def pb_cp_resConj (x : Residue) : Residue
  | 0 => x 2
  | 1 => x 1
  | 2 => x 0
  | 3 => x 3

private lemma pb_cp_resConj_eq (x : Residue) : pb_cp_resConj x = residueConjugate x := by
  ext i; fin_cases i <;> rfl

private def pb_cp_resNorm (x : Residue) : Residue := pb_cp_resMul (pb_cp_resConj x) x

private lemma pb_cp_resNorm_eq (x : Residue) : pb_cp_resNorm x = residueNorm x := by
  dsimp [pb_cp_resNorm, residueNorm]
  rw [pb_cp_resMul_eq, pb_cp_resConj_eq]

private abbrev pb_cp_resReducible (a : Residue) : Prop :=
  ∃ b : Residue, pb_cp_resMul (pb_cp_bits 10) b = a

private lemma pb_cp_resReducible_iff (a : Residue) : pb_cp_resReducible a ↔ Reducible a :=
  Iff.rfl

private def pb_cp_resOmegaPow : ℕ → Residue
  | 0 => pb_cp_bits 1
  | m + 1 => pb_cp_resMul (pb_cp_bits 2) (pb_cp_resOmegaPow m)

private abbrev pb_cp_weight2Irr (r : Residue) : Prop :=
  r = pb_cp_bits 3 ∨ r = pb_cp_bits 6 ∨ r = pb_cp_bits 9 ∨ r = pb_cp_bits 12

private lemma pb_cp_reducible_iff_norm_zero (x : Residue) :
    Reducible x ↔ residueNorm x = 0 := by
  rw [← pb_cp_resReducible_iff, ← pb_cp_resNorm_eq]
  revert x
  decide

private lemma pb_cp_reducible_iff_mul_bits10_zero (x : Residue) :
    Reducible x ↔ residueMultiply (bits 10) x = 0 := by
  rw [← pb_cp_resReducible_iff, ← pb_cp_resMul_eq, ← pb_cp_bits_eq]
  revert x
  decide

private lemma pb_cp_norm_eq_bits10_iff (r : Residue) :
    residueNorm r = bits 10 ↔ pb_cp_weight2Irr r := by
  rw [← pb_cp_resNorm_eq, ← pb_cp_bits_eq 10]
  revert r
  decide

private lemma pb_cp_norm_trichotomy (r : Residue) :
    Reducible r ∨ residueNorm r = bits 1 ∨ residueNorm r = bits 10 := by
  rw [← pb_cp_resReducible_iff, ← pb_cp_resNorm_eq, ← pb_cp_bits_eq 1, ← pb_cp_bits_eq 10]
  revert r
  decide

private lemma pb_cp_bits1_ne_zero : bits 1 ≠ (0 : Residue) := by
  rw [← pb_cp_bits_eq]; decide

private lemma pb_cp_bits10_ne_zero : bits 10 ≠ (0 : Residue) := by
  rw [← pb_cp_bits_eq]; decide

private lemma pb_cp_bits1_ne_bits10 : bits 1 ≠ bits 10 := by
  rw [← pb_cp_bits_eq 1, ← pb_cp_bits_eq 10]; decide

private lemma pb_cp_bits10_mul_bits15 : residueMultiply (bits 10) (bits 15) = 0 := by
  rw [← pb_cp_resMul_eq, ← pb_cp_bits_eq 10, ← pb_cp_bits_eq 15]; decide

private lemma pb_cp_bits10_sq_mul (c : Residue) :
    residueMultiply (bits 10) (residueMultiply (bits 10) c) = 0 := by
  rw [← pb_cp_resMul_eq, ← pb_cp_resMul_eq, ← pb_cp_bits_eq 10]
  revert c; decide

private lemma pb_cp_w2_pair_match (r1 r2 : Residue)
    (h1 : residueNorm r1 = bits 10) (h2 : residueNorm r2 = bits 10) :
    ∃ m : Fin 4, r1 + residueMultiply (pb_cp_resOmegaPow m.val) r2 = 0 := by
  simp only [← pb_cp_resNorm_eq, ← pb_cp_resMul_eq, ← pb_cp_bits_eq 10] at h1 h2 ⊢
  revert r1 r2 h1 h2
  decide

private lemma pb_cp_odd_pair_match (r1 r2 : Residue)
    (h1 : residueNorm r1 = bits 1) (h2 : residueNorm r2 = bits 1) :
    (∃ m : Fin 4, r1 + residueMultiply (pb_cp_resOmegaPow m.val) r2 = 0) ∨
    (∃ m : Fin 4, r1 + residueMultiply (pb_cp_resOmegaPow m.val) r2 = bits 15) := by
  simp only [← pb_cp_resNorm_eq, ← pb_cp_resMul_eq, ← pb_cp_bits_eq 1, ← pb_cp_bits_eq 15] at h1 h2 ⊢
  revert r1 r2 h1 h2
  decide

private lemma pb_cp_mul_bits10_eq_bits15_imp_w2 (w : Residue)
    (h : residueMultiply (bits 10) w = bits 15) : residueNorm w = bits 10 := by
  simp only [← pb_cp_resMul_eq, ← pb_cp_resNorm_eq, ← pb_cp_bits_eq 10, ← pb_cp_bits_eq 15] at h ⊢
  revert w h
  decide

private lemma pb_cp_mul_bits2_preserves_norm_w2 (w : Residue) (hw : residueNorm w = bits 10) :
    residueNorm (residueMultiply (bits 2) w) = bits 10 := by
  simp only [← pb_cp_resNorm_eq, ← pb_cp_resMul_eq, ← pb_cp_bits_eq 10, ← pb_cp_bits_eq 2] at hw ⊢
  revert w hw
  decide

private lemma pb_cp_resOmegaPow_mem (m : ℕ) :
    pb_cp_resOmegaPow m = pb_cp_bits 1 ∨ pb_cp_resOmegaPow m = pb_cp_bits 2 ∨
    pb_cp_resOmegaPow m = pb_cp_bits 4 ∨ pb_cp_resOmegaPow m = pb_cp_bits 8 := by
  induction m with
  | zero => exact Or.inl rfl
  | succ m ih =>
    rcases ih with h | h | h | h <;> dsimp [pb_cp_resOmegaPow] <;> rw [h]
    · exact Or.inr (Or.inl (by decide))
    · exact Or.inr (Or.inr (Or.inl (by decide)))
    · exact Or.inr (Or.inr (Or.inr (by decide)))
    · exact Or.inl (by decide)

private lemma pb_cp_mul_resOmegaPow_preserves_norm_w2 (m : ℕ) (w : Residue)
    (hw : residueNorm w = bits 10) :
    residueNorm (residueMultiply (pb_cp_resOmegaPow m) w) = bits 10 := by
  simp only [← pb_cp_resNorm_eq, ← pb_cp_resMul_eq, ← pb_cp_bits_eq 10] at hw ⊢
  rcases pb_cp_resOmegaPow_mem m with h | h | h | h <;> rw [h] <;> revert w hw <;> decide

/-! ## Part 2: Cyclotomic arithmetic in `Z[ω]` -/

noncomputable section

private def pb_cp_ω : ℂ := QAlgorithms.gateT true true

private def pb_cp_sqrtTwo : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

private lemma pb_cp_sqrtTwo_sq : pb_cp_sqrtTwo ^ 2 = 2 := by
  dsimp [pb_cp_sqrtTwo]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private lemma pb_cp_sqrtTwo_ne_zero : pb_cp_sqrtTwo ≠ 0 := by
  dsimp [pb_cp_sqrtTwo]
  exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'

private lemma pb_cp_ω_eq :
    pb_cp_ω = (((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I) := by
  dsimp [pb_cp_ω, QAlgorithms.gateT]
  rw [Matrix.diagonal_apply_eq]
  simp only [if_true]
  have harg : Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_mul_I]
  have hcos : Complex.cos ((Real.pi / 4 : ℝ) : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cos, Real.cos_pi_div_four]
  have hsin : Complex.sin ((Real.pi / 4 : ℝ) : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin, Real.sin_pi_div_four]
  rw [hcos, hsin]

private lemma pb_cp_ω_sq : pb_cp_ω ^ 2 = Complex.I := by
  rw [pb_cp_ω_eq, add_sq, mul_pow, Complex.I_sq]
  have h2 : (((Real.sqrt 2 / 2 : ℝ) : ℂ) ^ 2) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_pow, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  linear_combination (2 * Complex.I) * h2

private lemma pb_cp_ω_cube : pb_cp_ω ^ 3 =
    -(((Real.sqrt 2 / 2 : ℝ) : ℂ)) + (((Real.sqrt 2 / 2 : ℝ) : ℂ)) * Complex.I := by
  calc
    pb_cp_ω ^ 3 = pb_cp_ω ^ 2 * pb_cp_ω := by ring
    _ = Complex.I * (((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I) := by
      rw [pb_cp_ω_sq, pb_cp_ω_eq]
    _ = -(((Real.sqrt 2 / 2 : ℝ) : ℂ)) + (((Real.sqrt 2 / 2 : ℝ) : ℂ)) * Complex.I := by
      linear_combination ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I_sq

private lemma pb_cp_ω_pow_four : pb_cp_ω ^ 4 = -1 := by
  calc
    pb_cp_ω ^ 4 = (pb_cp_ω ^ 2) ^ 2 := by ring
    _ = Complex.I ^ 2 := by rw [pb_cp_ω_sq]
    _ = -1 := Complex.I_sq

private lemma pb_cp_ω_pow_eight : pb_cp_ω ^ 8 = 1 := by
  calc
    pb_cp_ω ^ 8 = (pb_cp_ω ^ 4) ^ 2 := by ring
    _ = (-1) ^ 2 := by rw [pb_cp_ω_pow_four]
    _ = 1 := by norm_num

private lemma pb_cp_ω_sub_cube : pb_cp_ω - pb_cp_ω ^ 3 = pb_cp_sqrtTwo := by
  have h1 := pb_cp_ω_eq
  have h3 := pb_cp_ω_cube
  dsimp [pb_cp_sqrtTwo]
  rw [h3, h1]
  push_cast
  ring

private lemma pb_cp_star_ω : star pb_cp_ω = -pb_cp_ω ^ 3 := by
  have h1 := pb_cp_ω_eq
  have h3 := pb_cp_ω_cube
  rw [h3, h1]
  simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

private lemma pb_cp_norm_ω : ‖pb_cp_ω‖ = 1 := by
  dsimp [pb_cp_ω, QAlgorithms.gateT]
  rw [Matrix.diagonal_apply_eq]
  simp only [if_true]
  have harg : Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

private def pb_cp_vec4 (x0 x1 x2 x3 : ℤ) : Fin 4 → ℤ
  | 0 => x0
  | 1 => x1
  | 2 => x2
  | 3 => x3

private def pb_cp_zOne : Fin 4 → ℤ := pb_cp_vec4 0 0 0 1
private def pb_cp_zOmega : Fin 4 → ℤ := pb_cp_vec4 0 0 1 0
private def pb_cp_zSqrtTwo : Fin 4 → ℤ := pb_cp_vec4 (-1) 0 1 0

private def pb_cp_zMul (a b : Fin 4 → ℤ) : Fin 4 → ℤ :=
  pb_cp_vec4
    (a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0)
    (a 1 * b 3 + a 2 * b 2 + a 3 * b 1 - a 0 * b 0)
    (a 2 * b 3 + a 3 * b 2 - a 0 * b 1 - a 1 * b 0)
    (a 3 * b 3 - a 0 * b 2 - a 1 * b 1 - a 2 * b 0)

private def pb_cp_zConj (a : Fin 4 → ℤ) : Fin 4 → ℤ :=
  pb_cp_vec4 (-a 2) (-a 1) (-a 0) (a 3)

private lemma pb_cp_omegaVal_zero : omegaCoordinatesValue (0 : Fin 4 → ℤ) = 0 := by
  simp [omegaCoordinatesValue]

private lemma pb_cp_omegaVal_zOne : omegaCoordinatesValue pb_cp_zOne = 1 := by
  dsimp [omegaCoordinatesValue, pb_cp_zOne, pb_cp_vec4]
  simp

private lemma pb_cp_omegaVal_zOmega : omegaCoordinatesValue pb_cp_zOmega = pb_cp_ω := by
  dsimp [omegaCoordinatesValue, pb_cp_zOmega, pb_cp_vec4, pb_cp_ω]
  simp

private lemma pb_cp_omegaVal_zSqrtTwo : omegaCoordinatesValue pb_cp_zSqrtTwo = pb_cp_sqrtTwo := by
  dsimp [omegaCoordinatesValue, pb_cp_zSqrtTwo, pb_cp_vec4]
  rw [← pb_cp_ω_sub_cube]
  dsimp [pb_cp_ω]
  ring

private lemma pb_cp_omegaVal_add (a b : Fin 4 → ℤ) :
    omegaCoordinatesValue (a + b) = omegaCoordinatesValue a + omegaCoordinatesValue b := by
  simp [omegaCoordinatesValue]
  ring

private lemma pb_cp_omegaVal_sub (a b : Fin 4 → ℤ) :
    omegaCoordinatesValue (a - b) = omegaCoordinatesValue a - omegaCoordinatesValue b := by
  simp [omegaCoordinatesValue]
  ring

private lemma pb_cp_omegaVal_neg (a : Fin 4 → ℤ) :
    omegaCoordinatesValue (-a) = -omegaCoordinatesValue a := by
  simp [omegaCoordinatesValue]
  ring

private lemma pb_cp_omegaVal_zMul (a b : Fin 4 → ℤ) :
    omegaCoordinatesValue (pb_cp_zMul a b) =
      omegaCoordinatesValue a * omegaCoordinatesValue b := by
  have h4 : (QAlgorithms.gateT true true) ^ 4 = (-1 : ℂ) := pb_cp_ω_pow_four
  have h5 : (QAlgorithms.gateT true true) ^ 5 = -(QAlgorithms.gateT true true) := by
    calc (QAlgorithms.gateT true true) ^ 5
        = (QAlgorithms.gateT true true) ^ 4 * QAlgorithms.gateT true true := by ring
      _ = -(QAlgorithms.gateT true true) := by rw [h4]; ring
  have h6 : (QAlgorithms.gateT true true) ^ 6 = -(QAlgorithms.gateT true true) ^ 2 := by
    calc (QAlgorithms.gateT true true) ^ 6
        = (QAlgorithms.gateT true true) ^ 4 * (QAlgorithms.gateT true true) ^ 2 := by ring
      _ = -(QAlgorithms.gateT true true) ^ 2 := by rw [h4]; ring
  dsimp [omegaCoordinatesValue, pb_cp_zMul, pb_cp_vec4]
  have hsplit : ((a 0 : ℂ) * QAlgorithms.gateT true true ^ 3 +
      (a 1 : ℂ) * QAlgorithms.gateT true true ^ 2 +
      (a 2 : ℂ) * QAlgorithms.gateT true true + (a 3 : ℂ)) *
    ((b 0 : ℂ) * QAlgorithms.gateT true true ^ 3 +
      (b 1 : ℂ) * QAlgorithms.gateT true true ^ 2 +
      (b 2 : ℂ) * QAlgorithms.gateT true true + (b 3 : ℂ)) =
    (a 0 : ℂ) * b 0 * QAlgorithms.gateT true true ^ 6 +
    ((a 0 : ℂ) * b 1 + a 1 * b 0) * QAlgorithms.gateT true true ^ 5 +
    ((a 0 : ℂ) * b 2 + a 1 * b 1 + a 2 * b 0) * QAlgorithms.gateT true true ^ 4 +
    ((a 0 : ℂ) * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0) * QAlgorithms.gateT true true ^ 3 +
    ((a 1 : ℂ) * b 3 + a 2 * b 2 + a 3 * b 1) * QAlgorithms.gateT true true ^ 2 +
    ((a 2 : ℂ) * b 3 + a 3 * b 2) * QAlgorithms.gateT true true + (a 3 : ℂ) * b 3 := by ring
  rw [hsplit, h6, h5, h4]
  push_cast
  ring

private lemma pb_cp_omegaVal_zConj (a : Fin 4 → ℤ) :
    omegaCoordinatesValue (pb_cp_zConj a) = star (omegaCoordinatesValue a) := by
  have hs1 : (starRingEnd ℂ) pb_cp_ω = -pb_cp_ω ^ 3 := pb_cp_star_ω
  have hsq : (-pb_cp_ω ^ 3) ^ 2 = -pb_cp_ω ^ 2 := by
    calc (-pb_cp_ω ^ 3) ^ 2 = pb_cp_ω ^ 4 * pb_cp_ω ^ 2 := by ring
      _ = -pb_cp_ω ^ 2 := by rw [pb_cp_ω_pow_four]; ring
  have hcu : (-pb_cp_ω ^ 3) ^ 3 = -pb_cp_ω := by
    calc (-pb_cp_ω ^ 3) ^ 3 = -(pb_cp_ω ^ 4) ^ 2 * pb_cp_ω := by ring
      _ = -pb_cp_ω := by rw [pb_cp_ω_pow_four]; ring
  change ((-a 2 : ℤ) : ℂ) * pb_cp_ω ^ 3 + ((-a 1 : ℤ) : ℂ) * pb_cp_ω ^ 2 +
      ((-a 0 : ℤ) : ℂ) * pb_cp_ω + (a 3 : ℂ) =
    star ((a 0 : ℂ) * pb_cp_ω ^ 3 + (a 1 : ℂ) * pb_cp_ω ^ 2 + (a 2 : ℂ) * pb_cp_ω + (a 3 : ℂ))
  simp only [star_add, star_mul, star_pow, Complex.star_def, map_intCast]
  rw [hs1, hsq, hcu]
  push_cast
  ring

private lemma pb_cp_int_add_int_mul_sqrtTwo_eq_zero {p q : ℤ}
    (h : (p : ℝ) + (q : ℝ) * Real.sqrt 2 = 0) : p = 0 ∧ q = 0 := by
  have hq : q = 0 := by
    by_contra hq0
    have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq0
    have hsqrt : Real.sqrt 2 = ((-p : ℤ) : ℝ) / (q : ℝ) := by
      field_simp [hqR]
      push_cast
      linarith
    have hrat : ((-p : ℤ) : ℝ) / (q : ℝ) = ((((-p : ℤ) : ℚ) / (q : ℚ) : ℚ) : ℝ) := by
      push_cast; rfl
    rw [hrat] at hsqrt
    exact irrational_sqrt_two ⟨((-p : ℤ) : ℚ) / (q : ℚ), hsqrt.symm⟩
  subst hq
  simp only [Int.cast_zero, zero_mul, add_zero] at h
  exact ⟨Int.cast_eq_zero.mp h, rfl⟩

private lemma pb_cp_omegaVal_eq_zero_iff (a : Fin 4 → ℤ) :
    omegaCoordinatesValue a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h' : (a 0 : ℂ) * pb_cp_ω ^ 3 + (a 1 : ℂ) * pb_cp_ω ^ 2 +
        (a 2 : ℂ) * pb_cp_ω + (a 3 : ℂ) = 0 := h
    rw [pb_cp_ω_cube, pb_cp_ω_sq, pb_cp_ω_eq] at h'
    have hre := congrArg Complex.re h'
    have him := congrArg Complex.im h'
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      Complex.zero_re, Complex.add_im, Complex.mul_im, Complex.neg_im, Complex.zero_im,
      mul_zero, sub_zero, zero_mul, add_zero, zero_add, mul_one] at hre him
    have hre2 : ((2 * a 3 : ℤ) : ℝ) + ((a 2 - a 0 : ℤ) : ℝ) * Real.sqrt 2 = 0 := by
      push_cast; linarith
    have him2 : ((2 * a 1 : ℤ) : ℝ) + ((a 2 + a 0 : ℤ) : ℝ) * Real.sqrt 2 = 0 := by
      push_cast; linarith
    obtain ⟨h3, h20⟩ := pb_cp_int_add_int_mul_sqrtTwo_eq_zero hre2
    obtain ⟨h1, h20'⟩ := pb_cp_int_add_int_mul_sqrtTwo_eq_zero him2
    have ha0 : a 0 = 0 := by omega
    have ha1 : a 1 = 0 := by omega
    have ha2 : a 2 = 0 := by omega
    have ha3 : a 3 = 0 := by omega
    ext i; fin_cases i <;> simp [ha0, ha1, ha2, ha3]
  · intro h; subst h; exact pb_cp_omegaVal_zero

private lemma pb_cp_omegaVal_injective : Function.Injective omegaCoordinatesValue := by
  intro a b h
  have hsub : omegaCoordinatesValue (a - b) = 0 := by
    rw [pb_cp_omegaVal_sub, h, sub_self]
  rw [pb_cp_omegaVal_eq_zero_iff] at hsub
  exact sub_eq_zero.mp hsub

private lemma pb_cp_omegaCoordinates_omegaVal (a : Fin 4 → ℤ) :
    omegaCoordinates (omegaCoordinatesValue a) = a := by
  have hmem : InZomega (omegaCoordinatesValue a) := ⟨a, rfl⟩
  rw [omegaCoordinates, dif_pos hmem]
  exact pb_cp_omegaVal_injective (Classical.choose_spec hmem)

private lemma pb_cp_residue_omegaVal (a : Fin 4 → ℤ) :
    residue (omegaCoordinatesValue a) = fun j => (a j : ZMod 2) := by
  unfold residue
  rw [pb_cp_omegaCoordinates_omegaVal]

private lemma pb_cp_inZomega_zero : InZomega 0 := ⟨0, pb_cp_omegaVal_zero⟩
private lemma pb_cp_inZomega_one : InZomega 1 := ⟨pb_cp_zOne, pb_cp_omegaVal_zOne⟩
private lemma pb_cp_inZomega_ω : InZomega pb_cp_ω := ⟨pb_cp_zOmega, pb_cp_omegaVal_zOmega⟩
private lemma pb_cp_inZomega_sqrtTwo : InZomega pb_cp_sqrtTwo := ⟨pb_cp_zSqrtTwo, pb_cp_omegaVal_zSqrtTwo⟩

private lemma pb_cp_inZomega_add {x y : ℂ} (hx : InZomega x) (hy : InZomega y) :
    InZomega (x + y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a + b, pb_cp_omegaVal_add a b⟩

private lemma pb_cp_inZomega_sub {x y : ℂ} (hx : InZomega x) (hy : InZomega y) :
    InZomega (x - y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a - b, pb_cp_omegaVal_sub a b⟩

private lemma pb_cp_inZomega_mul {x y : ℂ} (hx : InZomega x) (hy : InZomega y) :
    InZomega (x * y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨pb_cp_zMul a b, pb_cp_omegaVal_zMul a b⟩

private lemma pb_cp_inZomega_star {x : ℂ} (hx : InZomega x) : InZomega (star x) := by
  rcases hx with ⟨a, rfl⟩
  exact ⟨pb_cp_zConj a, pb_cp_omegaVal_zConj a⟩

private lemma pb_cp_inZomega_ω_pow (m : ℕ) : InZomega (pb_cp_ω ^ m) := by
  induction m with
  | zero => simpa using pb_cp_inZomega_one
  | succ m ih => rw [pow_succ]; exact pb_cp_inZomega_mul ih pb_cp_inZomega_ω

private lemma pb_cp_inZomega_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, InZomega (f i)) : InZomega (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using pb_cp_inZomega_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pb_cp_inZomega_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma pb_cp_residue_zero : residue 0 = 0 := by
  rw [← pb_cp_omegaVal_zero, pb_cp_residue_omegaVal]
  ext i; simp

private lemma pb_cp_residue_add {x y : ℂ} (hx : InZomega x) (hy : InZomega y) :
    residue (x + y) = residue x + residue y := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  rw [← pb_cp_omegaVal_add, pb_cp_residue_omegaVal, pb_cp_residue_omegaVal, pb_cp_residue_omegaVal]
  ext j; simp [Int.cast_add]

private lemma pb_cp_residue_sub {x y : ℂ} (hx : InZomega x) (hy : InZomega y) :
    residue (x - y) = residue x - residue y := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  rw [← pb_cp_omegaVal_sub, pb_cp_residue_omegaVal, pb_cp_residue_omegaVal, pb_cp_residue_omegaVal]
  ext j; simp [Int.cast_sub]

private lemma pb_cp_residue_mul {x y : ℂ} (hx : InZomega x) (hy : InZomega y) :
    residue (x * y) = residueMultiply (residue x) (residue y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  rw [← pb_cp_omegaVal_zMul, pb_cp_residue_omegaVal, pb_cp_residue_omegaVal, pb_cp_residue_omegaVal]
  ext l
  fin_cases l <;>
    simp [pb_cp_zMul, pb_cp_vec4, residueMultiply, Fin.sum_univ_four, Int.cast_add,
      Int.cast_mul, ZMod.neg_eq_self_mod_two, sub_eq_add_neg] <;>
    ring

private lemma pb_cp_residue_star {x : ℂ} (hx : InZomega x) :
    residue (star x) = residueConjugate (residue x) := by
  rcases hx with ⟨a, rfl⟩
  rw [← pb_cp_omegaVal_zConj, pb_cp_residue_omegaVal, pb_cp_residue_omegaVal]
  ext j
  fin_cases j <;>
    simp [pb_cp_zConj, pb_cp_vec4, residueConjugate, ZMod.neg_eq_self_mod_two]

private lemma pb_cp_residue_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, InZomega (f i)) :
    residue (∑ i ∈ s, f i) = ∑ i ∈ s, residue (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [pb_cp_residue_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, pb_cp_residue_add (hf a (Finset.mem_insert_self a s))
      (pb_cp_inZomega_sum s f fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      Finset.sum_insert ha, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

private lemma pb_cp_residue_sqrtTwo : residue pb_cp_sqrtTwo = bits 10 := by
  rw [← pb_cp_omegaVal_zSqrtTwo, pb_cp_residue_omegaVal]
  ext i
  fin_cases i <;> decide

private lemma pb_cp_residue_ω : residue pb_cp_ω = bits 2 := by
  rw [← pb_cp_omegaVal_zOmega, pb_cp_residue_omegaVal]
  ext i
  fin_cases i <;> decide

private lemma pb_cp_residue_ω_pow (m : ℕ) :
    residue (pb_cp_ω ^ m) = pb_cp_resOmegaPow m := by
  induction m with
  | zero =>
    simp only [pow_zero, pb_cp_resOmegaPow]
    rw [← pb_cp_omegaVal_zOne, pb_cp_residue_omegaVal]
    ext i; fin_cases i <;> decide
  | succ m ih =>
    rw [pow_succ', pb_cp_residue_mul pb_cp_inZomega_ω (pb_cp_inZomega_ω_pow m),
      pb_cp_residue_ω, ih, pb_cp_resOmegaPow, pb_cp_resMul_eq, pb_cp_bits_eq]

private lemma pb_cp_residue_two_pow {k : ℕ} (hk : 1 ≤ k) : residue ((2 : ℂ) ^ k) = 0 := by
  have hval : (2 : ℂ) ^ k = omegaCoordinatesValue (pb_cp_vec4 0 0 0 ((2 : ℤ) ^ k)) := by
    dsimp [omegaCoordinatesValue, pb_cp_vec4]
    simp
  rw [hval, pb_cp_residue_omegaVal]
  ext i
  fin_cases i
  · simp [pb_cp_vec4]
  · simp [pb_cp_vec4]
  · simp [pb_cp_vec4]
  · dsimp [pb_cp_vec4]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := rfl
    rw [h2, zero_pow (by omega)]

private lemma pb_cp_div_two_of_residue_zero {x : ℂ} (hx : InZomega x) (hr : residue x = 0) :
    InZomega (x / 2) := by
  rcases hx with ⟨a, rfl⟩
  rw [pb_cp_residue_omegaVal] at hr
  have hdiv : ∀ i : Fin 4, 2 ∣ a i := fun i => by
    have hi : ((a i : ZMod 2)) = 0 := congrFun hr i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) 2).mp hi
  refine ⟨fun i => a i / 2, ?_⟩
  have h2a : (2 : Fin 4 → ℤ) * (fun i => a i / 2) = a := by
    ext i
    exact Int.mul_ediv_cancel' (hdiv i)
  have hmul : omegaCoordinatesValue a = (2 : ℂ) * omegaCoordinatesValue (fun i => a i / 2) := by
    conv_lhs => rw [← h2a]
    simp [omegaCoordinatesValue]
    ring
  rw [hmul]
  ring

private lemma pb_cp_div_sqrtTwo_of_mul_bits10_zero {x : ℂ} (hx : InZomega x)
    (hr : residueMultiply (bits 10) (residue x) = 0) :
    InZomega (x / pb_cp_sqrtTwo) := by
  have hmul : InZomega (pb_cp_sqrtTwo * x) := pb_cp_inZomega_mul pb_cp_inZomega_sqrtTwo hx
  have hres : residue (pb_cp_sqrtTwo * x) = 0 := by
    rw [pb_cp_residue_mul pb_cp_inZomega_sqrtTwo hx, pb_cp_residue_sqrtTwo, hr]
  have hdiv2 : InZomega ((pb_cp_sqrtTwo * x) / 2) := pb_cp_div_two_of_residue_zero hmul hres
  have heq : (pb_cp_sqrtTwo * x) / 2 = x / pb_cp_sqrtTwo := by
    have hsq : (2 : ℂ) = pb_cp_sqrtTwo * pb_cp_sqrtTwo := by
      rw [← sq, pb_cp_sqrtTwo_sq]
    have hne : pb_cp_sqrtTwo ≠ 0 := pb_cp_sqrtTwo_ne_zero
    rw [hsq]
    field_simp [hne]
  rwa [heq] at hdiv2

/-! ## Part 3: Vector reduction over `Z[ω]` -/

private lemma pb_cp_mul_star_eq_normSq (z : ℂ) :
    z * star z = (Complex.normSq z : ℂ) := by
  rw [Complex.normSq_eq_norm_sq, Complex.ofReal_pow, Complex.star_def, Complex.mul_conj']

private lemma pb_cp_normSq_vec_sum {ι : Type*} [Fintype ι] (u : EuclideanSpace ℂ ι) :
    ‖u‖ ^ 2 = ∑ z : ι, Complex.normSq (u z) := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Complex.normSq_eq_norm_sq]

private lemma pb_cp_sum_norm_parity {u : EuclideanSpace ℂ (Qubits 2)} (hu : IsState u)
    {κ : ℕ} (hexp : VectorExponent u (κ + 1)) :
    Even (Finset.univ.filter fun z : Qubits 2 => residueNorm (kResidue (u z) (κ + 1)) = bits 1).card ∧
    Even (Finset.univ.filter fun z : Qubits 2 => residueNorm (kResidue (u z) (κ + 1)) = bits 10).card := by
  let X : Qubits 2 → ℂ := fun z => pb_cp_sqrtTwo ^ (κ + 1) * u z
  have hXin : ∀ z, InZomega (X z) := fun z => hexp z
  have hsum_X : ∑ z : Qubits 2, star (X z) * X z = (2 : ℂ) ^ (κ + 1) := by
    have hterm : ∀ z, star (X z) * X z = (2 : ℂ) ^ (κ + 1) * (Complex.normSq (u z) : ℂ) := by
      intro z
      dsimp [X]
      have hstar : star (pb_cp_sqrtTwo ^ (κ + 1)) = pb_cp_sqrtTwo ^ (κ + 1) := by
        dsimp [pb_cp_sqrtTwo]
        simp [Complex.conj_ofReal]
      calc star (pb_cp_sqrtTwo ^ (κ + 1) * u z) * (pb_cp_sqrtTwo ^ (κ + 1) * u z)
          = (star (pb_cp_sqrtTwo ^ (κ + 1)) * pb_cp_sqrtTwo ^ (κ + 1)) * (u z * star (u z)) := by
            rw [star_mul]; ring
        _ = (pb_cp_sqrtTwo ^ 2) ^ (κ + 1) * (Complex.normSq (u z) : ℂ) := by
            rw [hstar, pb_cp_mul_star_eq_normSq]; ring
        _ = (2 : ℂ) ^ (κ + 1) * (Complex.normSq (u z) : ℂ) := by
            rw [pb_cp_sqrtTwo_sq]
    simp_rw [hterm, ← Finset.mul_sum]
    have hnorm : ∑ z : Qubits 2, (Complex.normSq (u z) : ℂ) = 1 := by
      have h1 : ‖u‖ ^ 2 = 1 := by rw [hu, one_pow]
      rw [pb_cp_normSq_vec_sum] at h1
      exact_mod_cast h1
    rw [hnorm, mul_one]
  have hres_sum : ∑ z : Qubits 2, residueNorm (kResidue (u z) (κ + 1)) = 0 := by
    have h0 := congrArg residue hsum_X
    rw [pb_cp_residue_sum Finset.univ _ (fun z _ => pb_cp_inZomega_mul (pb_cp_inZomega_star (hXin z)) (hXin z)),
      pb_cp_residue_two_pow (by omega)] at h0
    refine h0.symm.trans ?_ |>.symm
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [pb_cp_residue_mul (pb_cp_inZomega_star (hXin z)) (hXin z), pb_cp_residue_star (hXin z)]
    rfl
  have hcoord3 : ((Finset.univ.filter fun z : Qubits 2 =>
      residueNorm (kResidue (u z) (κ + 1)) = bits 1).card : ZMod 2) = 0 := by
    have hc := congrFun hres_sum 3
    simp only [Finset.sum_apply, Pi.zero_apply] at hc
    have hterm3 : ∀ z : Qubits 2, (residueNorm (kResidue (u z) (κ + 1))) 3 =
        if residueNorm (kResidue (u z) (κ + 1)) = bits 1 then (1 : ZMod 2) else 0 := by
      intro z
      rcases pb_cp_norm_trichotomy (kResidue (u z) (κ + 1)) with hr | hr | hr
      · rw [pb_cp_reducible_iff_norm_zero] at hr
        rw [hr, if_neg pb_cp_bits1_ne_zero.symm]; rfl
      · rw [hr, if_pos rfl]; decide
      · rw [hr, if_neg pb_cp_bits1_ne_bits10.symm]; decide
    simp_rw [hterm3, Finset.sum_boole] at hc
    exact hc
  have hcoord0 : ((Finset.univ.filter fun z : Qubits 2 =>
      residueNorm (kResidue (u z) (κ + 1)) = bits 10).card : ZMod 2) = 0 := by
    have hc := congrFun hres_sum 0
    simp only [Finset.sum_apply, Pi.zero_apply] at hc
    have hterm0 : ∀ z : Qubits 2, (residueNorm (kResidue (u z) (κ + 1))) 0 =
        if residueNorm (kResidue (u z) (κ + 1)) = bits 10 then (1 : ZMod 2) else 0 := by
      intro z
      rcases pb_cp_norm_trichotomy (kResidue (u z) (κ + 1)) with hr | hr | hr
      · rw [pb_cp_reducible_iff_norm_zero] at hr
        rw [hr, if_neg pb_cp_bits10_ne_zero.symm]; rfl
      · rw [hr, if_neg pb_cp_bits1_ne_bits10]; decide
      · rw [hr, if_pos rfl]; decide
    simp_rw [hterm0, Finset.sum_boole] at hc
    exact hc
  constructor
  · obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ 2).mp hcoord3
    exact ⟨k, by omega⟩
  · obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ 2).mp hcoord0
    exact ⟨k, by omega⟩

private def pb_cp_twoLevelVec (m : Fin 8) (j l : Qubits 2)
    (u : EuclideanSpace ℂ (Qubits 2)) : EuclideanSpace ℂ (Qubits 2) :=
  WithLp.toLp 2 fun z =>
    if z = j then (u j + pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹
    else if z = l then pb_cp_ω ^ ((8 - m.val) % 8) * ((u j - pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹)
    else u z

private lemma pb_cp_twoLevelVec_isState (m : Fin 8) {j l : Qubits 2} (hjl : j ≠ l)
    {u : EuclideanSpace ℂ (Qubits 2)} (hu : IsState u) :
    IsState (pb_cp_twoLevelVec m j l u) := by
  have hsq1 : ‖pb_cp_twoLevelVec m j l u‖ ^ 2 = 1 := by
    rw [pb_cp_normSq_vec_sum]
    have hu' : ∑ z : Qubits 2, Complex.normSq (u z) = 1 := by
      rw [← pb_cp_normSq_vec_sum, hu, one_pow]
    rw [← hu']
    have hrest : ∀ z : Qubits 2, z ≠ j → z ≠ l →
        Complex.normSq (pb_cp_twoLevelVec m j l u z) = Complex.normSq (u z) := by
      intro z hzj hzl
      simp [pb_cp_twoLevelVec, hzj, hzl]
    have hpair : Complex.normSq (pb_cp_twoLevelVec m j l u j) +
        Complex.normSq (pb_cp_twoLevelVec m j l u l) =
        Complex.normSq (u j) + Complex.normSq (u l) := by
      have hlj : l ≠ j := hjl.symm
      have hj_val : pb_cp_twoLevelVec m j l u j = (u j + pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹ := by
        simp [pb_cp_twoLevelVec]
      have hl_val : pb_cp_twoLevelVec m j l u l =
          pb_cp_ω ^ ((8 - m.val) % 8) * ((u j - pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹) := by
        simp [pb_cp_twoLevelVec, hlj]
      rw [hj_val, hl_val]
      have hnorm_pow : ∀ k : ℕ, Complex.normSq (pb_cp_ω ^ k) = 1 := fun k => by
        rw [Complex.normSq_eq_norm_sq, norm_pow, pb_cp_norm_ω, one_pow, one_pow]
      have hnorm_s2 : Complex.normSq (pb_cp_sqrtTwo⁻¹) = 1 / 2 := by
        rw [Complex.normSq_inv, Complex.normSq_eq_norm_sq]
        dsimp [pb_cp_sqrtTwo]
        rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
        norm_num
      simp only [Complex.normSq_mul, hnorm_pow, one_mul, hnorm_s2]
      have hpara : ∀ a b : ℂ, Complex.normSq (a + b) + Complex.normSq (a - b) =
          2 * Complex.normSq a + 2 * Complex.normSq b := by
        intro a b; simp [Complex.normSq_apply]; ring
      have hcomb := hpara (u j) (pb_cp_ω ^ m.val * u l)
      rw [Complex.normSq_mul, hnorm_pow, one_mul] at hcomb
      linarith
    have hsum_split : ∀ f : Qubits 2 → ℝ,
        ∑ z : Qubits 2, f z = f j + f l +
          ∑ z ∈ (Finset.univ.erase j).erase l, f z := fun f => by
      have hj_mem : j ∈ (Finset.univ : Finset (Qubits 2)) := Finset.mem_univ j
      have hl_mem : l ∈ (Finset.univ : Finset (Qubits 2)).erase j :=
        Finset.mem_erase.mpr ⟨hjl.symm, Finset.mem_univ l⟩
      rw [← Finset.add_sum_erase Finset.univ f hj_mem,
        ← Finset.add_sum_erase ((Finset.univ : Finset (Qubits 2)).erase j) f hl_mem]
      ring
    rw [hsum_split (fun z => Complex.normSq (pb_cp_twoLevelVec m j l u z)),
      hsum_split (fun z => Complex.normSq (u z)), hpair]
    congr 1
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [Finset.mem_erase, Finset.mem_erase] at hz
    exact hrest z hz.2.1 hz.1
  rw [IsState]
  nlinarith [norm_nonneg (pb_cp_twoLevelVec m j l u)]

private lemma pb_cp_twoLevel_reduce_same_orbit {κ : ℕ} {u : EuclideanSpace ℂ (Qubits 2)}
    (hexp : VectorExponent u (κ + 1)) {j l : Qubits 2} (hjl : j ≠ l) (m : Fin 8)
    (hm : kResidue (u j) (κ + 1) + residueMultiply (pb_cp_resOmegaPow m.val) (kResidue (u l) (κ + 1)) = 0) :
    VectorExponent (pb_cp_twoLevelVec m j l u) (κ + 1) ∧
    ScalarExponent (pb_cp_twoLevelVec m j l u j) κ ∧
    ScalarExponent (pb_cp_twoLevelVec m j l u l) κ := by
  let Xj := pb_cp_sqrtTwo ^ (κ + 1) * u j
  let Xl := pb_cp_sqrtTwo ^ (κ + 1) * u l
  have hXj : InZomega Xj := hexp j
  have hXl : InZomega Xl := hexp l
  have hωm : InZomega (pb_cp_ω ^ m.val) := pb_cp_inZomega_ω_pow m.val
  have hωinv : InZomega (pb_cp_ω ^ ((8 - m.val) % 8)) := pb_cp_inZomega_ω_pow ((8 - m.val) % 8)
  have hplus_in : InZomega (Xj + pb_cp_ω ^ m.val * Xl) :=
    pb_cp_inZomega_add hXj (pb_cp_inZomega_mul hωm hXl)
  have hminus_in : InZomega (Xj - pb_cp_ω ^ m.val * Xl) :=
    pb_cp_inZomega_sub hXj (pb_cp_inZomega_mul hωm hXl)
  have hplus_res : residue (Xj + pb_cp_ω ^ m.val * Xl) = 0 := by
    rw [pb_cp_residue_add hXj (pb_cp_inZomega_mul hωm hXl),
      pb_cp_residue_mul hωm hXl, pb_cp_residue_ω_pow]
    exact hm
  have hminus_res : residue (Xj - pb_cp_ω ^ m.val * Xl) = 0 := by
    rw [pb_cp_residue_sub hXj (pb_cp_inZomega_mul hωm hXl),
      pb_cp_residue_mul hωm hXl, pb_cp_residue_ω_pow]
    ext i
    have hi := congrFun hm i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
    exact hi
  have hdiv_plus : InZomega ((Xj + pb_cp_ω ^ m.val * Xl) / 2) :=
    pb_cp_div_two_of_residue_zero hplus_in hplus_res
  have hdiv_minus : InZomega ((Xj - pb_cp_ω ^ m.val * Xl) / 2) :=
    pb_cp_div_two_of_residue_zero hminus_in hminus_res
  have hsc_j : ScalarExponent (pb_cp_twoLevelVec m j l u j) κ := by
    rw [ScalarExponent]
    have hj_val : pb_cp_twoLevelVec m j l u j = (u j + pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹ := by
      simp [pb_cp_twoLevelVec]
    rw [hj_val]
    have heq : ((Real.sqrt 2 : ℝ) : ℂ) ^ κ * ((u j + pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹) =
        (Xj + pb_cp_ω ^ m.val * Xl) / 2 := by
      dsimp [Xj, Xl]
      have hsq : (2 : ℂ) = pb_cp_sqrtTwo * pb_cp_sqrtTwo := by rw [← sq, pb_cp_sqrtTwo_sq]
      have hs : ((Real.sqrt 2 : ℝ) : ℂ) = pb_cp_sqrtTwo := rfl
      have hne : pb_cp_sqrtTwo ≠ 0 := pb_cp_sqrtTwo_ne_zero
      rw [hs, hsq, pow_succ]
      field_simp [hne]
    rwa [heq]
  have hsc_l : ScalarExponent (pb_cp_twoLevelVec m j l u l) κ := by
    rw [ScalarExponent]
    have hl_val : pb_cp_twoLevelVec m j l u l =
        pb_cp_ω ^ ((8 - m.val) % 8) * ((u j - pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹) := by
      simp [pb_cp_twoLevelVec, hjl.symm]
    rw [hl_val]
    have heq : ((Real.sqrt 2 : ℝ) : ℂ) ^ κ *
          (pb_cp_ω ^ ((8 - m.val) % 8) * ((u j - pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹)) =
        pb_cp_ω ^ ((8 - m.val) % 8) * ((Xj - pb_cp_ω ^ m.val * Xl) / 2) := by
      dsimp [Xj, Xl]
      have hsq : (2 : ℂ) = pb_cp_sqrtTwo * pb_cp_sqrtTwo := by rw [← sq, pb_cp_sqrtTwo_sq]
      have hs : ((Real.sqrt 2 : ℝ) : ℂ) = pb_cp_sqrtTwo := rfl
      have hne : pb_cp_sqrtTwo ≠ 0 := pb_cp_sqrtTwo_ne_zero
      rw [hs, hsq, pow_succ]
      field_simp [hne]
    rw [heq]
    exact pb_cp_inZomega_mul hωinv hdiv_minus
  have hlift : ∀ {t : ℂ}, ScalarExponent t κ → ScalarExponent t (κ + 1) := by
    intro t ht
    rw [ScalarExponent, pow_succ', mul_assoc]
    exact pb_cp_inZomega_mul pb_cp_inZomega_sqrtTwo ht
  refine ⟨fun z => ?_, hsc_j, hsc_l⟩
  by_cases hzj : z = j
  · subst hzj; exact hlift hsc_j
  · by_cases hzl : z = l
    · subst hzl; exact hlift hsc_l
    · have hz_val : pb_cp_twoLevelVec m j l u z = u z := by simp [pb_cp_twoLevelVec, hzj, hzl]
      rw [hz_val]; exact hexp z

private lemma pb_cp_twoLevel_reduce_mixed_odd {κ : ℕ} {u : EuclideanSpace ℂ (Qubits 2)}
    (hexp : VectorExponent u (κ + 1)) {j l : Qubits 2} (hjl : j ≠ l) (m : Fin 8)
    (hm : kResidue (u j) (κ + 1) + residueMultiply (pb_cp_resOmegaPow m.val) (kResidue (u l) (κ + 1)) = bits 15) :
    VectorExponent (pb_cp_twoLevelVec m j l u) (κ + 1) ∧
    residueNorm (kResidue (pb_cp_twoLevelVec m j l u j) (κ + 1)) = bits 10 ∧
    residueNorm (kResidue (pb_cp_twoLevelVec m j l u l) (κ + 1)) = bits 10 := by
  let Xj := pb_cp_sqrtTwo ^ (κ + 1) * u j
  let Xl := pb_cp_sqrtTwo ^ (κ + 1) * u l
  have hXj : InZomega Xj := hexp j
  have hXl : InZomega Xl := hexp l
  have hωm : InZomega (pb_cp_ω ^ m.val) := pb_cp_inZomega_ω_pow m.val
  have hωinv : InZomega (pb_cp_ω ^ ((8 - m.val) % 8)) := pb_cp_inZomega_ω_pow ((8 - m.val) % 8)
  have hplus_in : InZomega (Xj + pb_cp_ω ^ m.val * Xl) :=
    pb_cp_inZomega_add hXj (pb_cp_inZomega_mul hωm hXl)
  have hminus_in : InZomega (Xj - pb_cp_ω ^ m.val * Xl) :=
    pb_cp_inZomega_sub hXj (pb_cp_inZomega_mul hωm hXl)
  have hplus_res : residue (Xj + pb_cp_ω ^ m.val * Xl) = bits 15 := by
    rw [pb_cp_residue_add hXj (pb_cp_inZomega_mul hωm hXl),
      pb_cp_residue_mul hωm hXl, pb_cp_residue_ω_pow]
    exact hm
  have hminus_res : residue (Xj - pb_cp_ω ^ m.val * Xl) = bits 15 := by
    rw [pb_cp_residue_sub hXj (pb_cp_inZomega_mul hωm hXl),
      pb_cp_residue_mul hωm hXl, pb_cp_residue_ω_pow]
    rw [← hm]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
    rfl
  have hm_bits10_plus : residueMultiply (bits 10) (residue (Xj + pb_cp_ω ^ m.val * Xl)) = 0 := by
    rw [hplus_res]; exact pb_cp_bits10_mul_bits15
  have hm_bits10_minus : residueMultiply (bits 10) (residue (Xj - pb_cp_ω ^ m.val * Xl)) = 0 := by
    rw [hminus_res]; exact pb_cp_bits10_mul_bits15
  have hdiv_plus : InZomega ((Xj + pb_cp_ω ^ m.val * Xl) / pb_cp_sqrtTwo) :=
    pb_cp_div_sqrtTwo_of_mul_bits10_zero hplus_in hm_bits10_plus
  have hdiv_minus : InZomega ((Xj - pb_cp_ω ^ m.val * Xl) / pb_cp_sqrtTwo) :=
    pb_cp_div_sqrtTwo_of_mul_bits10_zero hminus_in hm_bits10_minus
  have hsc_j : ScalarExponent (pb_cp_twoLevelVec m j l u j) (κ + 1) := by
    rw [ScalarExponent]
    have hj_val : pb_cp_twoLevelVec m j l u j = (u j + pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹ := by
      simp [pb_cp_twoLevelVec]
    rw [hj_val]
    have heq : ((Real.sqrt 2 : ℝ) : ℂ) ^ (κ + 1) * ((u j + pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹) =
        (Xj + pb_cp_ω ^ m.val * Xl) / pb_cp_sqrtTwo := by
      dsimp [Xj, Xl]; have hs : ((Real.sqrt 2 : ℝ) : ℂ) = pb_cp_sqrtTwo := rfl; rw [hs]; ring
    rwa [heq]
  have hsc_l : ScalarExponent (pb_cp_twoLevelVec m j l u l) (κ + 1) := by
    rw [ScalarExponent]
    have hl_val : pb_cp_twoLevelVec m j l u l =
        pb_cp_ω ^ ((8 - m.val) % 8) * ((u j - pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹) := by
      simp [pb_cp_twoLevelVec, hjl.symm]
    rw [hl_val]
    have heq : ((Real.sqrt 2 : ℝ) : ℂ) ^ (κ + 1) *
          (pb_cp_ω ^ ((8 - m.val) % 8) * ((u j - pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹)) =
        pb_cp_ω ^ ((8 - m.val) % 8) * ((Xj - pb_cp_ω ^ m.val * Xl) / pb_cp_sqrtTwo) := by
      dsimp [Xj, Xl]; have hs : ((Real.sqrt 2 : ℝ) : ℂ) = pb_cp_sqrtTwo := rfl; rw [hs]; ring
    rw [heq]
    exact pb_cp_inZomega_mul hωinv hdiv_minus
  have hw2_j : residueNorm (kResidue (pb_cp_twoLevelVec m j l u j) (κ + 1)) = bits 10 := by
    have hj_val : pb_cp_twoLevelVec m j l u j = (u j + pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹ := by
      simp [pb_cp_twoLevelVec]
    have heq : ((Real.sqrt 2 : ℝ) : ℂ) ^ (κ + 1) * pb_cp_twoLevelVec m j l u j =
        (Xj + pb_cp_ω ^ m.val * Xl) / pb_cp_sqrtTwo := by
      rw [hj_val]; dsimp [Xj, Xl]; have hs : ((Real.sqrt 2 : ℝ) : ℂ) = pb_cp_sqrtTwo := rfl; rw [hs]; ring
    dsimp [kResidue]
    rw [heq]
    apply pb_cp_mul_bits10_eq_bits15_imp_w2
    rw [← pb_cp_residue_sqrtTwo, ← pb_cp_residue_mul pb_cp_inZomega_sqrtTwo hdiv_plus]
    have hmul : pb_cp_sqrtTwo * ((Xj + pb_cp_ω ^ m.val * Xl) / pb_cp_sqrtTwo) =
        Xj + pb_cp_ω ^ m.val * Xl := mul_div_cancel₀ _ pb_cp_sqrtTwo_ne_zero
    rw [hmul, hplus_res]
  have hw2_l : residueNorm (kResidue (pb_cp_twoLevelVec m j l u l) (κ + 1)) = bits 10 := by
    have hl_val : pb_cp_twoLevelVec m j l u l =
        pb_cp_ω ^ ((8 - m.val) % 8) * ((u j - pb_cp_ω ^ m.val * u l) * pb_cp_sqrtTwo⁻¹) := by
      simp [pb_cp_twoLevelVec, hjl.symm]
    have heq : ((Real.sqrt 2 : ℝ) : ℂ) ^ (κ + 1) * pb_cp_twoLevelVec m j l u l =
        pb_cp_ω ^ ((8 - m.val) % 8) * ((Xj - pb_cp_ω ^ m.val * Xl) / pb_cp_sqrtTwo) := by
      rw [hl_val]; dsimp [Xj, Xl]; have hs : ((Real.sqrt 2 : ℝ) : ℂ) = pb_cp_sqrtTwo := rfl; rw [hs]; ring
    dsimp [kResidue]
    rw [heq, pb_cp_residue_mul hωinv hdiv_minus, pb_cp_residue_ω_pow]
    apply pb_cp_mul_resOmegaPow_preserves_norm_w2
    apply pb_cp_mul_bits10_eq_bits15_imp_w2
    rw [← pb_cp_residue_sqrtTwo, ← pb_cp_residue_mul pb_cp_inZomega_sqrtTwo hdiv_minus]
    have hmul : pb_cp_sqrtTwo * ((Xj - pb_cp_ω ^ m.val * Xl) / pb_cp_sqrtTwo) =
        Xj - pb_cp_ω ^ m.val * Xl := mul_div_cancel₀ _ pb_cp_sqrtTwo_ne_zero
    rw [hmul, hminus_res]
  refine ⟨fun z => ?_, hw2_j, hw2_l⟩
  by_cases hzj : z = j
  · subst hzj; exact hsc_j
  · by_cases hzl : z = l
    · subst hzl; exact hsc_l
    · have hz_val : pb_cp_twoLevelVec m j l u z = u z := by simp [pb_cp_twoLevelVec, hzj, hzl]
      rw [hz_val]; exact hexp z

private lemma pb_cp_finset_two_elems_of_even_pos {α : Type*} [DecidableEq α]
    {s : Finset α} (heven : Even s.card) (hne : s.Nonempty) :
    ∃ j l : α, j ∈ s ∧ l ∈ s ∧ j ≠ l := by
  obtain ⟨j, hj⟩ := hne
  have hne2 : (s.erase j).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hcard : s.card = 1 := by
      have := Finset.card_erase_add_one hj
      rw [h, Finset.card_empty, zero_add] at this
      exact this.symm
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨l, hl⟩ := hne2
  rw [Finset.mem_erase] at hl
  exact ⟨j, l, hj, hl.2, hl.1.symm⟩

private lemma pb_cp_finset_card_drop_two {α : Type*} [DecidableEq α]
    {s s' : Finset α} {j l : α} (hjl : j ≠ l) (hj : j ∈ s) (hl : l ∈ s)
    (hj' : j ∉ s') (hl' : l ∉ s')
    (hrest : ∀ z, z ≠ j → z ≠ l → (z ∈ s' ↔ z ∈ s)) :
    s'.card + 2 = s.card := by
  have heq : s' = (s.erase j).erase l := by
    ext z
    simp only [Finset.mem_erase]
    by_cases hzj : z = j
    · subst hzj; simp [hj']
    · by_cases hzl : z = l
      · subst hzl; simp [hl']
      · simp [hzj, hzl, hrest z hzj hzl]
  rw [heq]
  have hl_er : l ∈ s.erase j := Finset.mem_erase.mpr ⟨hjl.symm, hl⟩
  have h1 := Finset.card_erase_add_one hl_er
  have h2 := Finset.card_erase_add_one hj
  omega

private lemma pb_cp_finset_card_add_two {α : Type*} [DecidableEq α]
    {s s' : Finset α} {j l : α} (hjl : j ≠ l) (hj : j ∉ s) (hl : l ∉ s)
    (hj' : j ∈ s') (hl' : l ∈ s')
    (hrest : ∀ z, z ≠ j → z ≠ l → (z ∈ s' ↔ z ∈ s)) :
    s.card + 2 = s'.card :=
  pb_cp_finset_card_drop_two hjl hj' hl' hj hl (fun z hzj hzl => (hrest z hzj hzl).symm)

private lemma pb_cp_finset_card_same {α : Type*} [DecidableEq α]
    {s s' : Finset α} {j l : α}
    (hj : j ∈ s' ↔ j ∈ s) (hl : l ∈ s' ↔ l ∈ s)
    (hrest : ∀ z, z ≠ j → z ≠ l → (z ∈ s' ↔ z ∈ s)) :
    s'.card = s.card := by
  have heq : s' = s := by
    ext z
    by_cases hzj : z = j
    · subst hzj; exact hj
    · by_cases hzl : z = l
      · subst hzl; exact hl
      · exact hrest z hzj hzl
  rw [heq]

private def pb_cp_n1 (κ : ℕ) (u : EuclideanSpace ℂ (Qubits 2)) : ℕ :=
  (Finset.univ.filter fun z : Qubits 2 => residueNorm (kResidue (u z) (κ + 1)) = bits 1).card

private def pb_cp_n10 (κ : ℕ) (u : EuclideanSpace ℂ (Qubits 2)) : ℕ :=
  (Finset.univ.filter fun z : Qubits 2 => residueNorm (kResidue (u z) (κ + 1)) = bits 10).card

private lemma pb_cp_potential_le_eight (κ : ℕ) (u : EuclideanSpace ℂ (Qubits 2)) :
    2 * pb_cp_n1 κ u + pb_cp_n10 κ u ≤ 8 := by
  have hdisj : Disjoint
      (Finset.univ.filter fun z : Qubits 2 => residueNorm (kResidue (u z) (κ + 1)) = bits 1)
      (Finset.univ.filter fun z : Qubits 2 => residueNorm (kResidue (u z) (κ + 1)) = bits 10) := by
    rw [Finset.disjoint_filter]
    intro z _ h1 h10
    exact pb_cp_bits1_ne_bits10 (h1.symm.trans h10)
  have hsum : pb_cp_n1 κ u + pb_cp_n10 κ u ≤ 4 := by
    rw [pb_cp_n1, pb_cp_n10, ← Finset.card_union_of_disjoint hdisj]
    calc ((Finset.univ.filter _ ∪ Finset.univ.filter _).card)
        ≤ (Finset.univ : Finset (Qubits 2)).card := Finset.card_le_univ _
      _ = 4 := by decide
  omega

private lemma pb_cp_kResidue_succ_of_scalar {z : ℂ} {κ : ℕ} (hz : ScalarExponent z κ) :
    Reducible (kResidue z (κ + 1)) := by
  rw [pb_cp_reducible_iff_mul_bits10_zero]
  dsimp [kResidue]
  have heq : ((Real.sqrt 2 : ℝ) : ℂ) ^ (κ + 1) * z = pb_cp_sqrtTwo * (((Real.sqrt 2 : ℝ) : ℂ) ^ κ * z) := by
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) = pb_cp_sqrtTwo := rfl
    rw [hs, pow_succ']; ring
  rw [heq, pb_cp_residue_mul pb_cp_inZomega_sqrtTwo hz, pb_cp_residue_sqrtTwo]
  exact pb_cp_bits10_sq_mul _

private lemma pb_cp_step_helper_zero {κ : ℕ} {u : EuclideanSpace ℂ (Qubits 2)}
    (hu : IsState u) (hexp : VectorExponent u (κ + 1))
    {j l : Qubits 2} (hjl : j ≠ l) (m : Fin 8)
    (hj_norm : residueNorm (kResidue (u j) (κ + 1)) = bits 1 ∨ residueNorm (kResidue (u j) (κ + 1)) = bits 10)
    (_hl_norm : residueNorm (kResidue (u l) (κ + 1)) = bits 1 ∨ residueNorm (kResidue (u l) (κ + 1)) = bits 10)
    (hsame : residueNorm (kResidue (u j) (κ + 1)) = residueNorm (kResidue (u l) (κ + 1)))
    (hm : kResidue (u j) (κ + 1) + residueMultiply (pb_cp_resOmegaPow m.val) (kResidue (u l) (κ + 1)) = 0) :
    IsState (pb_cp_twoLevelVec m j l u) ∧
    VectorExponent (pb_cp_twoLevelVec m j l u) (κ + 1) ∧
    2 * pb_cp_n1 κ (pb_cp_twoLevelVec m j l u) + pb_cp_n10 κ (pb_cp_twoLevelVec m j l u) + 2 ≤
      2 * pb_cp_n1 κ u + pb_cp_n10 κ u := by
  obtain ⟨hexp', hscj, hscl⟩ := pb_cp_twoLevel_reduce_same_orbit hexp hjl m hm
  have hu' := pb_cp_twoLevelVec_isState m hjl hu
  have hredj : residueNorm (kResidue (pb_cp_twoLevelVec m j l u j) (κ + 1)) = 0 :=
    (pb_cp_reducible_iff_norm_zero _).mp (pb_cp_kResidue_succ_of_scalar hscj)
  have hredl : residueNorm (kResidue (pb_cp_twoLevelVec m j l u l) (κ + 1)) = 0 :=
    (pb_cp_reducible_iff_norm_zero _).mp (pb_cp_kResidue_succ_of_scalar hscl)
  have hrest : ∀ z, z ≠ j → z ≠ l → pb_cp_twoLevelVec m j l u z = u z := fun z hzj hzl => by
    simp [pb_cp_twoLevelVec, hzj, hzl]
  refine ⟨hu', hexp', ?_⟩
  rcases hj_norm with hj1 | hj10
  · have hl1 : residueNorm (kResidue (u l) (κ + 1)) = bits 1 := hsame.symm.trans hj1
    have hn1 : pb_cp_n1 κ (pb_cp_twoLevelVec m j l u) + 2 = pb_cp_n1 κ u := by
      refine pb_cp_finset_card_drop_two hjl ?_ ?_ ?_ ?_ ?_
      · simp [hj1]
      · simp [hl1]
      · simp [hredj, pb_cp_bits1_ne_zero.symm]
      · simp [hredl, pb_cp_bits1_ne_zero.symm]
      · intro z hzj hzl; simp [hrest z hzj hzl]
    have hn10 : pb_cp_n10 κ (pb_cp_twoLevelVec m j l u) = pb_cp_n10 κ u := by
      refine pb_cp_finset_card_same (j := j) (l := l) ?_ ?_ ?_
      · simp [hredj, hj1, pb_cp_bits10_ne_zero.symm, pb_cp_bits1_ne_bits10]
      · simp [hredl, hl1, pb_cp_bits10_ne_zero.symm, pb_cp_bits1_ne_bits10]
      · intro z hzj hzl; simp [hrest z hzj hzl]
    omega
  · have hl10 : residueNorm (kResidue (u l) (κ + 1)) = bits 10 := hsame.symm.trans hj10
    have hn1 : pb_cp_n1 κ (pb_cp_twoLevelVec m j l u) = pb_cp_n1 κ u := by
      refine pb_cp_finset_card_same (j := j) (l := l) ?_ ?_ ?_
      · simp [hredj, hj10, pb_cp_bits1_ne_zero.symm, pb_cp_bits1_ne_bits10.symm]
      · simp [hredl, hl10, pb_cp_bits1_ne_zero.symm, pb_cp_bits1_ne_bits10.symm]
      · intro z hzj hzl; simp [hrest z hzj hzl]
    have hn10 : pb_cp_n10 κ (pb_cp_twoLevelVec m j l u) + 2 = pb_cp_n10 κ u := by
      refine pb_cp_finset_card_drop_two hjl ?_ ?_ ?_ ?_ ?_
      · simp [hj10]
      · simp [hl10]
      · simp [hredj, pb_cp_bits10_ne_zero.symm]
      · simp [hredl, pb_cp_bits10_ne_zero.symm]
      · intro z hzj hzl; simp [hrest z hzj hzl]
    omega

private lemma pb_cp_single_step_reduce {κ : ℕ} {u : EuclideanSpace ℂ (Qubits 2)}
    (hu : IsState u) (hexp : VectorExponent u (κ + 1))
    (hpos : 0 < 2 * pb_cp_n1 κ u + pb_cp_n10 κ u) :
    ∃ (m : Fin 8) (j l : Qubits 2) (_hjl : j ≠ l),
      IsState (pb_cp_twoLevelVec m j l u) ∧
      VectorExponent (pb_cp_twoLevelVec m j l u) (κ + 1) ∧
      2 * pb_cp_n1 κ (pb_cp_twoLevelVec m j l u) + pb_cp_n10 κ (pb_cp_twoLevelVec m j l u) + 2 ≤
        2 * pb_cp_n1 κ u + pb_cp_n10 κ u := by
  obtain ⟨heven1, heven10⟩ := pb_cp_sum_norm_parity hu hexp
  by_cases h10_pos : 0 < pb_cp_n10 κ u
  · have hne : (Finset.univ.filter fun z : Qubits 2 =>
        residueNorm (kResidue (u z) (κ + 1)) = bits 10).Nonempty := Finset.card_pos.mp h10_pos
    obtain ⟨j, l, hj, hl, hjl⟩ := pb_cp_finset_two_elems_of_even_pos heven10 hne
    rw [Finset.mem_filter] at hj hl
    obtain ⟨m4, hm4⟩ := pb_cp_w2_pair_match _ _ hj.2 hl.2
    let m : Fin 8 := ⟨m4.val, by omega⟩
    obtain ⟨hu', hexp', hpot'⟩ := pb_cp_step_helper_zero hu hexp hjl m
      (Or.inr hj.2) (Or.inr hl.2) (hj.2.trans hl.2.symm) hm4
    exact ⟨m, j, l, hjl, hu', hexp', hpot'⟩
  · have h1_pos : 0 < pb_cp_n1 κ u := by omega
    have hne : (Finset.univ.filter fun z : Qubits 2 =>
        residueNorm (kResidue (u z) (κ + 1)) = bits 1).Nonempty := Finset.card_pos.mp h1_pos
    obtain ⟨j, l, hj, hl, hjl⟩ := pb_cp_finset_two_elems_of_even_pos heven1 hne
    rw [Finset.mem_filter] at hj hl
    rcases pb_cp_odd_pair_match _ _ hj.2 hl.2 with ⟨m4, hm4⟩ | ⟨m4, hm4⟩
    · let m : Fin 8 := ⟨m4.val, by omega⟩
      obtain ⟨hu', hexp', hpot'⟩ := pb_cp_step_helper_zero hu hexp hjl m
        (Or.inl hj.2) (Or.inl hl.2) (hj.2.trans hl.2.symm) hm4
      exact ⟨m, j, l, hjl, hu', hexp', hpot'⟩
    · let m : Fin 8 := ⟨m4.val, by omega⟩
      obtain ⟨hexp', h10j, h10l⟩ := pb_cp_twoLevel_reduce_mixed_odd hexp hjl m hm4
      have hu' := pb_cp_twoLevelVec_isState m hjl hu
      have hrest : ∀ z, z ≠ j → z ≠ l → pb_cp_twoLevelVec m j l u z = u z := fun z hzj hzl => by
        simp [pb_cp_twoLevelVec, hzj, hzl]
      have hn1 : pb_cp_n1 κ (pb_cp_twoLevelVec m j l u) + 2 = pb_cp_n1 κ u := by
        refine pb_cp_finset_card_drop_two hjl ?_ ?_ ?_ ?_ ?_
        · simp [hj.2]
        · simp [hl.2]
        · simp [h10j, pb_cp_bits1_ne_bits10.symm]
        · simp [h10l, pb_cp_bits1_ne_bits10.symm]
        · intro z hzj hzl; simp [hrest z hzj hzl]
      have hn10 : pb_cp_n10 κ u + 2 = pb_cp_n10 κ (pb_cp_twoLevelVec m j l u) := by
        refine pb_cp_finset_card_add_two hjl ?_ ?_ ?_ ?_ ?_
        · simp [hj.2, pb_cp_bits1_ne_bits10]
        · simp [hl.2, pb_cp_bits1_ne_bits10]
        · simp [h10j]
        · simp [h10l]
        · intro z hzj hzl; simp [hrest z hzj hzl]
      exact ⟨m, j, l, hjl, hu', hexp', by omega⟩

/-! ## Part 4: Base case (`κ = 0`) -/

private lemma pb_cp_normSq_omegaVal (a : Fin 4 → ℤ) :
    Complex.normSq (omegaCoordinatesValue a) =
      ((a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 : ℤ) : ℝ) +
      ((a 2 * a 3 + a 1 * a 2 + a 0 * a 1 - a 3 * a 0 : ℤ) : ℝ) * Real.sqrt 2 := by
  let p : ℤ := a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2
  let q : ℤ := a 2 * a 3 + a 1 * a 2 + a 0 * a 1 - a 3 * a 0
  have hmul : pb_cp_zMul (pb_cp_zConj a) a = pb_cp_vec4 (-q) 0 q p := by
    ext i
    fin_cases i <;> simp [pb_cp_zMul, pb_cp_zConj, pb_cp_vec4, p, q] <;> ring
  have hC : (Complex.normSq (omegaCoordinatesValue a) : ℂ) = (p : ℂ) + (q : ℂ) * pb_cp_sqrtTwo := by
    calc (Complex.normSq (omegaCoordinatesValue a) : ℂ)
        = omegaCoordinatesValue a * star (omegaCoordinatesValue a) :=
          (pb_cp_mul_star_eq_normSq _).symm
      _ = star (omegaCoordinatesValue a) * omegaCoordinatesValue a := mul_comm _ _
      _ = omegaCoordinatesValue (pb_cp_zMul (pb_cp_zConj a) a) := by
          rw [← pb_cp_omegaVal_zConj, ← pb_cp_omegaVal_zMul]
      _ = omegaCoordinatesValue (pb_cp_vec4 (-q) 0 q p) := by rw [hmul]
      _ = (p : ℂ) + (q : ℂ) * (pb_cp_ω - pb_cp_ω ^ 3) := by
          dsimp [omegaCoordinatesValue, pb_cp_vec4, pb_cp_ω]
          push_cast; ring
      _ = (p : ℂ) + (q : ℂ) * pb_cp_sqrtTwo := by rw [pb_cp_ω_sub_cube]
  have hre := congrArg Complex.re hC
  dsimp [p, q] at hre
  simpa [pb_cp_sqrtTwo] using hre

private lemma pb_cp_base_case_vec {u : EuclideanSpace ℂ (Qubits 2)} (hu : IsState u)
    (hexp : VectorExponent u 0) :
    ∃ (z₀ : Qubits 2) (r : Fin 8), u = (pb_cp_ω ^ r.val) • ket z₀ := by
  classical
  have hexp' : ∀ z, InZomega (u z) := fun z => by
    have hz := hexp z
    simpa [ScalarExponent] using hz
  choose c hc using hexp'
  let P : Qubits 2 → ℤ := fun z => c z 0 ^ 2 + c z 1 ^ 2 + c z 2 ^ 2 + c z 3 ^ 2
  let Q : Qubits 2 → ℤ := fun z => c z 2 * c z 3 + c z 1 * c z 2 + c z 0 * c z 1 - c z 3 * c z 0
  have hnorm1 : (1 : ℝ) = ((∑ z, P z : ℤ) : ℝ) + ((∑ z, Q z : ℤ) : ℝ) * Real.sqrt 2 := by
    have h1 : ‖u‖ ^ 2 = 1 := by rw [hu, one_pow]
    rw [pb_cp_normSq_vec_sum] at h1
    have hsum : ∑ z : Qubits 2, Complex.normSq (u z) =
        ∑ z : Qubits 2, ((P z : ℝ) + (Q z : ℝ) * Real.sqrt 2) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← hc z, pb_cp_normSq_omegaVal]
    rw [hsum, Finset.sum_add_distrib, ← Finset.sum_mul] at h1
    push_cast
    exact h1.symm
  have hzero : ((1 - ∑ z, P z : ℤ) : ℝ) + ((-∑ z, Q z : ℤ) : ℝ) * Real.sqrt 2 = 0 := by
    push_cast at hnorm1 ⊢
    linarith
  obtain ⟨hP1, _⟩ := pb_cp_int_add_int_mul_sqrtTwo_eq_zero hzero
  have hsumP : ∑ z : Qubits 2, ∑ i : Fin 4, (c z i) ^ 2 = 1 := by
    have hPeq : ∑ z : Qubits 2, P z = 1 := by omega
    rw [← hPeq]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [P, Fin.sum_univ_four]
  have hprod : ∑ p : Qubits 2 × Fin 4, (c p.1 p.2) ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    exact hsumP
  have hex : ∃ p₀ : Qubits 2 × Fin 4, (c p₀.1 p₀.2) ^ 2 = 1 ∧
      ∀ p : Qubits 2 × Fin 4, p ≠ p₀ → c p.1 p.2 = 0 := by
    have hne : ∃ p₀ : Qubits 2 × Fin 4, c p₀.1 p₀.2 ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : ∑ p : Qubits 2 × Fin 4, (c p.1 p.2) ^ 2 = 0 :=
        Finset.sum_eq_zero fun p _ => by simp [h p]
      omega
    obtain ⟨p₀, hp₀⟩ := hne
    have habs : 1 ≤ |c p₀.1 p₀.2| := Int.one_le_abs hp₀
    have hp₀_sq : 1 ≤ (c p₀.1 p₀.2) ^ 2 := by
      nlinarith [sq_abs (c p₀.1 p₀.2)]
    have hrest_nonneg : ∀ p : Qubits 2 × Fin 4, 0 ≤ (c p.1 p.2) ^ 2 := fun p => sq_nonneg _
    have hsplit := Finset.add_sum_erase Finset.univ (fun p : Qubits 2 × Fin 4 => (c p.1 p.2) ^ 2)
      (Finset.mem_univ p₀)
    rw [hprod] at hsplit
    have hsum_er_nonneg : 0 ≤ ∑ p ∈ Finset.univ.erase p₀, (c p.1 p.2) ^ 2 :=
      Finset.sum_nonneg fun p _ => hrest_nonneg p
    have hp₀_eq : (c p₀.1 p₀.2) ^ 2 = 1 := by omega
    have hsum_er_zero : ∑ p ∈ Finset.univ.erase p₀, (c p.1 p.2) ^ 2 = 0 := by omega
    refine ⟨p₀, hp₀_eq, fun p hp => ?_⟩
    have hmem : p ∈ Finset.univ.erase p₀ := Finset.mem_erase.mpr ⟨hp, Finset.mem_univ p⟩
    have hsq0 : (c p.1 p.2) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun q _ => hrest_nonneg q).mp hsum_er_zero p hmem
    exact sq_eq_zero_iff.mp hsq0
  obtain ⟨⟨z₀, i₀⟩, hsq1, hother⟩ := hex
  have hsign : c z₀ i₀ = 1 ∨ c z₀ i₀ = -1 := by
    have hsq : (c z₀ i₀ - 1) * (c z₀ i₀ + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hsq with h | h <;> [left; right] <;> omega
  have hω_at : ∃ r : Fin 8, omegaCoordinatesValue (c z₀) = pb_cp_ω ^ r.val := by
    have hc_other : ∀ i : Fin 4, i ≠ i₀ → c z₀ i = 0 := fun i hi =>
      hother (z₀, i) (fun heq => hi (congrArg Prod.snd heq))
    have hval : omegaCoordinatesValue (c z₀) = (c z₀ i₀ : ℂ) * pb_cp_ω ^ (3 - i₀.val) := by
      dsimp [omegaCoordinatesValue, pb_cp_ω]
      fin_cases i₀
      · rw [hc_other 1 (by decide), hc_other 2 (by decide), hc_other 3 (by decide)]; simp
      · rw [hc_other 0 (by decide), hc_other 2 (by decide), hc_other 3 (by decide)]; simp
      · rw [hc_other 0 (by decide), hc_other 1 (by decide), hc_other 3 (by decide)]; simp
      · rw [hc_other 0 (by decide), hc_other 1 (by decide), hc_other 2 (by decide)]; simp
    rcases hsign with hpos | hneg
    · refine ⟨⟨3 - i₀.val, by omega⟩, ?_⟩
      rw [hval, hpos, Int.cast_one, one_mul]
    · refine ⟨⟨7 - i₀.val, by omega⟩, ?_⟩
      rw [hval, hneg, Int.cast_neg, Int.cast_one, neg_one_mul]
      have hexp8 : (⟨7 - i₀.val, by omega⟩ : Fin 8).val = 4 + (3 - i₀.val) := by
        dsimp; omega
      rw [hexp8, pow_add, pb_cp_ω_pow_four, neg_one_mul]
  obtain ⟨r, hr⟩ := hω_at
  refine ⟨z₀, r, ?_⟩
  ext z
  simp only [PiLp.smul_apply, smul_eq_mul, ket, PiLp.single_apply]
  by_cases hz : z = z₀
  · subst hz
    rw [if_pos rfl, mul_one, ← hc z, hr]
  · rw [if_neg hz, mul_zero, ← hc z]
    have hcz : c z = 0 := by
      ext i
      exact hother (z, i) (fun heq => hz (congrArg Prod.fst heq))
    rw [hcz, pb_cp_omegaVal_zero]

/-! ## Part 5: Gadget interface & circuit assembly -/

private structure PbCpGadgets where
  invCirc : Circuit htcxGateSet (1 + 2) → Circuit htcxGateSet (1 + 2)
  invCirc_size : ∀ c, (invCirc c).size ≤ 7 * c.size
  invCirc_prepares : ∀ (c : Circuit htcxGateSet (1 + 2)) (v : EuclideanSpace ℂ (Qubits 2)),
    (∀ w : EuclideanSpace ℂ (Qubits 2), act c.unitary (dataTensor false w) = dataTensor false w) →
    act c.unitary (dataTensor true v) = dataTensor true (ket fun _ => false) →
    PreparesControlled (invCirc c).unitary v
  append_unitary : ∀ c1 c2 : Circuit htcxGateSet (1 + 2),
    (c1 ++ c2).unitary = c2.unitary * c1.unitary
  append_size : ∀ c1 c2 : Circuit htcxGateSet (1 + 2),
    (c1 ++ c2).size = c1.size + c2.size
  nil_unitary : Circuit.unitary ([] : Circuit htcxGateSet (1 + 2)) = 1
  nil_size : Circuit.size ([] : Circuit htcxGateSet (1 + 2)) = 0
  ctrlOmegaPow : Fin 8 → Circuit htcxGateSet (1 + 2)
  ctrlOmegaPow_size : ∀ m, (ctrlOmegaPow m).size ≤ 7
  ctrlOmegaPow_false : ∀ m w, act (ctrlOmegaPow m).unitary (dataTensor false w) = dataTensor false w
  ctrlOmegaPow_true : ∀ m u,
    act (ctrlOmegaPow m).unitary (dataTensor true u) = dataTensor true ((pb_cp_ω ^ m.val) • u)
  ctrlSwap : ∀ (j l : Qubits 2), j ≠ l → Circuit htcxGateSet (1 + 2)
  ctrlSwap_size : ∀ j l (hjl : j ≠ l), (ctrlSwap j l hjl).size ≤ 100
  ctrlSwap_false : ∀ j l (hjl : j ≠ l) w,
    act (ctrlSwap j l hjl).unitary (dataTensor false w) = dataTensor false w
  ctrlSwap_true : ∀ j l (hjl : j ≠ l) u,
    act (ctrlSwap j l hjl).unitary (dataTensor true u) =
      dataTensor true (WithLp.toLp 2 fun z => u (Equiv.swap j l z))
  ctrlTwoLevel : Fin 8 → ∀ (j l : Qubits 2), j ≠ l → Circuit htcxGateSet (1 + 2)
  ctrlTwoLevel_size : ∀ m j l (hjl : j ≠ l), (ctrlTwoLevel m j l hjl).size ≤ 200
  ctrlTwoLevel_false : ∀ m j l (hjl : j ≠ l) w,
    act (ctrlTwoLevel m j l hjl).unitary (dataTensor false w) = dataTensor false w
  ctrlTwoLevel_true : ∀ m j l (hjl : j ≠ l) u,
    act (ctrlTwoLevel m j l hjl).unitary (dataTensor true u) =
      dataTensor true (pb_cp_twoLevelVec m j l u)

private lemma pb_cp_act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext z
  simp [act, Matrix.mulVec_mulVec]

private lemma pb_cp_act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  ext z
  simp [act]

private lemma pb_cp_reduce_pass (G : PbCpGadgets) (κ : ℕ) :
    ∀ (N : ℕ) (u : EuclideanSpace ℂ (Qubits 2)),
      IsState u → VectorExponent u (κ + 1) → 2 * pb_cp_n1 κ u + pb_cp_n10 κ u ≤ 2 * N →
      ∃ (c : Circuit htcxGateSet (1 + 2)) (u' : EuclideanSpace ℂ (Qubits 2)),
        c.size ≤ 200 * N ∧
        IsState u' ∧
        VectorExponent u' κ ∧
        (∀ w, act c.unitary (dataTensor false w) = dataTensor false w) ∧
        act c.unitary (dataTensor true u) = dataTensor true u' := by
  intro N
  induction N with
  | zero =>
    intro u hu hexp hpot
    have hn1 : pb_cp_n1 κ u = 0 := by omega
    have hn10 : pb_cp_n10 κ u = 0 := by omega
    have hexpκ : VectorExponent u κ := by
      intro z
      have hz1 : residueNorm (kResidue (u z) (κ + 1)) ≠ bits 1 := by
        intro h
        have hmem : z ∈ Finset.univ.filter fun w : Qubits 2 =>
            residueNorm (kResidue (u w) (κ + 1)) = bits 1 := Finset.mem_filter.mpr ⟨Finset.mem_univ z, h⟩
        have hpos : 0 < pb_cp_n1 κ u := Finset.card_pos.mpr ⟨z, hmem⟩
        omega
      have hz10 : residueNorm (kResidue (u z) (κ + 1)) ≠ bits 10 := by
        intro h
        have hmem : z ∈ Finset.univ.filter fun w : Qubits 2 =>
            residueNorm (kResidue (u w) (κ + 1)) = bits 10 := Finset.mem_filter.mpr ⟨Finset.mem_univ z, h⟩
        have hpos : 0 < pb_cp_n10 κ u := Finset.card_pos.mpr ⟨z, hmem⟩
        omega
      have hred : Reducible (kResidue (u z) (κ + 1)) := by
        rcases pb_cp_norm_trichotomy (kResidue (u z) (κ + 1)) with h | h | h
        · exact h
        · exact absurd h hz1
        · exact absurd h hz10
      rw [pb_cp_reducible_iff_mul_bits10_zero] at hred
      have hdiv := pb_cp_div_sqrtTwo_of_mul_bits10_zero (hexp z) hred
      have heq : (((Real.sqrt 2 : ℝ) : ℂ) ^ (κ + 1) * u z) / pb_cp_sqrtTwo =
          ((Real.sqrt 2 : ℝ) : ℂ) ^ κ * u z := by
        have hs : ((Real.sqrt 2 : ℝ) : ℂ) = pb_cp_sqrtTwo := rfl
        have hne : pb_cp_sqrtTwo ≠ 0 := pb_cp_sqrtTwo_ne_zero
        rw [hs, pow_succ]
        field_simp [hne]
      rwa [heq] at hdiv
    refine ⟨([] : Circuit htcxGateSet (1 + 2)), u, ?_, hu, hexpκ, fun w => ?_, ?_⟩
    · have := G.nil_size; omega
    · rw [G.nil_unitary, pb_cp_act_one]
    · rw [G.nil_unitary, pb_cp_act_one]
  | succ N ih =>
    intro u hu hexp hpot
    by_cases h0 : 2 * pb_cp_n1 κ u + pb_cp_n10 κ u = 0
    · obtain ⟨c, u', hsize, hu', hexp', hfalse, htrue⟩ := ih u hu hexp (by omega)
      exact ⟨c, u', by omega, hu', hexp', hfalse, htrue⟩
    · have hpos : 0 < 2 * pb_cp_n1 κ u + pb_cp_n10 κ u := Nat.pos_of_ne_zero h0
      obtain ⟨m, j, l, hjl, hu1, hexp1, hpot1⟩ := pb_cp_single_step_reduce hu hexp hpos
      have hpot1' : 2 * pb_cp_n1 κ (pb_cp_twoLevelVec m j l u) +
          pb_cp_n10 κ (pb_cp_twoLevelVec m j l u) ≤ 2 * N := by omega
      obtain ⟨c2, u', hc2size, hu', hexp', hc2false, hc2true⟩ :=
        ih (pb_cp_twoLevelVec m j l u) hu1 hexp1 hpot1'
      refine ⟨G.ctrlTwoLevel m j l hjl ++ c2, u', ?_, hu', hexp', fun w => ?_, ?_⟩
      · rw [G.append_size]
        have hc1size := G.ctrlTwoLevel_size m j l hjl
        omega
      · rw [G.append_unitary, pb_cp_act_mul, G.ctrlTwoLevel_false, hc2false]
      · rw [G.append_unitary, pb_cp_act_mul, G.ctrlTwoLevel_true, hc2true]

private lemma pb_cp_reduce_to_ket0 (G : PbCpGadgets) :
    ∀ (κ : ℕ) (u : EuclideanSpace ℂ (Qubits 2)),
      IsState u → VectorExponent u κ →
      ∃ c : Circuit htcxGateSet (1 + 2),
        c.size ≤ 800 * κ + 107 ∧
        (∀ w, act c.unitary (dataTensor false w) = dataTensor false w) ∧
        act c.unitary (dataTensor true u) = dataTensor true (ket fun _ => false) := by
  intro κ
  induction κ with
  | zero =>
    intro u hu hexp
    obtain ⟨z₀, r, rfl⟩ := pb_cp_base_case_vec hu hexp
    let z00 : Qubits 2 := fun _ => false
    let cSwap : Circuit htcxGateSet (1 + 2) :=
      if h : z₀ = z00 then ([] : Circuit htcxGateSet (1 + 2)) else G.ctrlSwap z₀ z00 h
    have hcSwap_size : cSwap.size ≤ 100 := by
      dsimp [cSwap]
      split_ifs
      · have := G.nil_size; omega
      · exact G.ctrlSwap_size z₀ z00 _
    have hcSwap_false : ∀ w, act cSwap.unitary (dataTensor false w) = dataTensor false w := by
      intro w
      dsimp [cSwap]
      split_ifs
      · rw [G.nil_unitary, pb_cp_act_one]
      · exact G.ctrlSwap_false z₀ z00 _ w
    have hcSwap_true :
        act cSwap.unitary (dataTensor true ((pb_cp_ω ^ r.val) • ket z₀)) =
          dataTensor true ((pb_cp_ω ^ r.val) • ket z00) := by
      dsimp [cSwap]
      split_ifs with hz
      · subst hz; rw [G.nil_unitary, pb_cp_act_one]
      · rw [G.ctrlSwap_true]
        congr 1
        ext z
        simp only [PiLp.smul_apply, smul_eq_mul, ket, PiLp.single_apply]
        have hswap_iff : (Equiv.swap z₀ z00 z = z₀) ↔ (z = z00) := by
          conv_lhs => rhs; rw [← Equiv.swap_apply_right z₀ z00]
          exact (Equiv.swap z₀ z00).injective.eq_iff
        simp only [hswap_iff]
    let rInv : Fin 8 := ⟨(8 - r.val) % 8, Nat.mod_lt _ (by decide)⟩
    let cPhase := G.ctrlOmegaPow rInv
    have hcPhase_size : cPhase.size ≤ 7 := G.ctrlOmegaPow_size rInv
    have hcPhase_false : ∀ w, act cPhase.unitary (dataTensor false w) = dataTensor false w :=
      G.ctrlOmegaPow_false rInv
    have hcPhase_true :
        act cPhase.unitary (dataTensor true ((pb_cp_ω ^ r.val) • ket z00)) =
          dataTensor true (ket z00) := by
      rw [G.ctrlOmegaPow_true]
      congr 1
      rw [smul_smul, ← pow_add]
      have h8 : rInv.val + r.val = 0 ∨ rInv.val + r.val = 8 := by
        dsimp [rInv]
        omega
      rcases h8 with h | h <;> rw [h]
      · simp
      · rw [pb_cp_ω_pow_eight, one_smul]
    refine ⟨cSwap ++ cPhase, ?_, fun w => ?_, ?_⟩
    · rw [G.append_size]; omega
    · rw [G.append_unitary, pb_cp_act_mul, hcSwap_false, hcPhase_false]
    · rw [G.append_unitary, pb_cp_act_mul, hcSwap_true, hcPhase_true]
  | succ κ ih =>
    intro u hu hexp
    obtain ⟨c1, u1, hc1size, hu1, hexp1, hc1false, hc1true⟩ :=
      pb_cp_reduce_pass G κ 4 u hu hexp (pb_cp_potential_le_eight κ u)
    obtain ⟨c2, hc2size, hc2false, hc2true⟩ := ih u1 hu1 hexp1
    refine ⟨c1 ++ c2, ?_, fun w => ?_, ?_⟩
    · rw [G.append_size]; omega
    · rw [G.append_unitary, pb_cp_act_mul, hc1false, hc2false]
    · rw [G.append_unitary, pb_cp_act_mul, hc1true, hc2true]

private theorem pb_cp_solution_from_gadgets (G : PbCpGadgets) :
    ∃ A : ℝ, 0 < A ∧ ∀ (k : ℕ) (v : EuclideanSpace ℂ (Qubits 2)),
      IsState v →
      (∀ z, ∃ a b : ℤ, v z = ((a : ℂ) + (b : ℂ) * Complex.I) / (2 : ℂ) ^ k) →
      ∃ c : Circuit htcxGateSet (1 + 2),
        PreparesControlled c.unitary v ∧
        (c.size : ℝ) ≤ A * ((k : ℝ) + 1) := by
  refine ⟨11200, by norm_num, fun k v hv hrat => ?_⟩
  have hexp : VectorExponent v (2 * k) := by
    intro z
    obtain ⟨a, b, hzv⟩ := hrat z
    rw [ScalarExponent, hzv]
    have hpow : ((Real.sqrt 2 : ℝ) : ℂ) ^ (2 * k) = (2 : ℂ) ^ k := by
      have hs : ((Real.sqrt 2 : ℝ) : ℂ) = pb_cp_sqrtTwo := rfl
      rw [hs, pow_mul, pb_cp_sqrtTwo_sq]
    have h2ne : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    rw [hpow, mul_div_cancel₀ _ h2ne]
    refine ⟨pb_cp_vec4 0 b 0 a, ?_⟩
    dsimp [omegaCoordinatesValue, pb_cp_vec4]
    have hsq : (QAlgorithms.gateT true true) ^ 2 = Complex.I := pb_cp_ω_sq
    rw [hsq]
    ring
  obtain ⟨cRed, hcRedSize, hcRedFalse, hcRedTrue⟩ := pb_cp_reduce_to_ket0 G (2 * k) v hv hexp
  refine ⟨G.invCirc cRed, G.invCirc_prepares cRed v hcRedFalse hcRedTrue, ?_⟩
  have hinvSize : (G.invCirc cRed).size ≤ 7 * cRed.size := G.invCirc_size cRed
  have hbound : (G.invCirc cRed).size ≤ 11200 * (k + 1) := by omega
  exact_mod_cast hbound


private def pb_cp_gadgets : PbCpGadgets where
  invCirc := pb_cg_invCirc
  invCirc_size := pb_cg_invCirc_size
  invCirc_prepares := pb_cg_preparesControlled_of_reduces
  append_unitary := pb_cg_unitary_append
  append_size := pb_cg_size_append
  nil_unitary := pb_cg_unitary_nil
  nil_size := rfl
  ctrlOmegaPow := pb_cg_ctrlOmegaPow
  ctrlOmegaPow_size := pb_cg_ctrlOmegaPow_size
  ctrlOmegaPow_false := pb_cg_ctrlOmegaPow_false
  ctrlOmegaPow_true := pb_cg_ctrlOmegaPow_true
  ctrlSwap := pb_cg_ctrlSwap
  ctrlSwap_size := pb_cg_ctrlSwap_size
  ctrlSwap_false := pb_cg_ctrlSwap_false
  ctrlSwap_true := pb_cg_ctrlSwap_true
  ctrlTwoLevel := pb_cg_ctrlTwoLevel
  ctrlTwoLevel_size := pb_cg_ctrlTwoLevel_size
  ctrlTwoLevel_false := pb_cg_ctrlTwoLevel_false
  ctrlTwoLevel_true := pb_cg_ctrlTwoLevel_true

end

theorem solution :
    ∃ A : ℝ, 0 < A ∧ ∀ (k : ℕ) (v : EuclideanSpace ℂ (QAlgorithms.Qubits 2)),
      QAlgorithms.IsState v →
      (∀ z, ∃ a b : ℤ, v z = ((a : ℂ) + (b : ℂ) * Complex.I) / (2 : ℂ) ^ k) →
      ∃ c : QAlgorithms.Circuit QAlgorithms.htcxGateSet (1 + 2),
        CliffordTApprox.Ancilla.PreparesControlled c.unitary v ∧
        (c.size : ℝ) ≤ A * ((k : ℝ) + 1) :=
  pb_cp_solution_from_gadgets pb_cp_gadgets
