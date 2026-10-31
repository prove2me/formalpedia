-- Prove2me | solution 1 for CliffordTApprox.Ancilla.phase_gate_approx
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:59:04.696025+00:00
-- url     : https://prove2.me/submissions/79d8f134-19ae-43c6-b2f1-2b4fdd2a1a07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CliffordTApprox_Ancilla_Setting
import Theorems.Thm_CliffordTApprox_Ancilla_phase_reduction
import Theorems.Thm_CliffordTApprox_Ancilla_four_square_unit_vector
import Theorems.Thm_CliffordTApprox_Ancilla_controlled_preparation
import Theorems.Thm_CliffordTApprox_Ancilla_state_distance

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12
open CliffordTApprox.Ancilla

noncomputable section

def dT (b : Bool) : ℂ := if b then Complex.exp (Complex.I * Real.pi / 4) else 1

lemma norm_exp_I_pi_div_four : ‖Complex.exp (Complex.I * Real.pi / 4)‖ = 1 := by
  have h : Complex.I * (Real.pi / 4 : ℂ) = ((Real.pi / 4 : ℝ) * Complex.I) := by
    push_cast; ring
  have h2 : Complex.I * Real.pi / 4 = Complex.I * (Real.pi / 4 : ℂ) := by ring
  rw [h2, h, Complex.norm_exp_ofReal_mul_I]

lemma norm_dT (b : Bool) : ‖dT b‖ = 1 := by
  cases b
  · simp [dT]
  · simp [dT, norm_exp_I_pi_div_four]

lemma norm_dT_pow (b : Bool) (m : ℕ) : ‖(dT b) ^ m‖ = 1 := by
  rw [norm_pow, norm_dT, one_pow]

lemma qubits1_ext (u v : Qubits 1) (h : u 0 = v 0) : u = v := by
  ext i
  fin_cases i
  exact h

lemma qubitsAppendEquiv_fst_zero (y : Qubits (1 + 2)) :
    (qubitsAppendEquiv 1 2 y).1 0 = y 0 := rfl

lemma diagonal_mul_apply {m n : Type*} [Fintype m] [DecidableEq m] (d : m → ℂ) (M : Matrix m n ℂ) (i : m) (j : n) :
    (Matrix.diagonal d * M) i j = d i * M i j := by
  simp [Matrix.mul_apply, Matrix.diagonal]

lemma diagonal_pow {m : Type*} [Fintype m] [DecidableEq m] (d : m → ℂ) (k : ℕ) :
    (Matrix.diagonal d) ^ k = Matrix.diagonal (fun i => d i ^ k) := by
  induction k with
  | zero =>
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal]
  | succ k ih =>
    rw [pow_succ', ih]
    ext i j
    rw [diagonal_mul_apply]
    simp only [Matrix.diagonal, Matrix.of_apply]
    split_ifs with h
    · rw [← pow_succ']
    · ring

def tWire : Fin (Gate.ofMatrix1 gateT).arity ↪ Fin (1 + 2) where
  toFun _ := 0
  inj' := by
    change ∀ i j : Fin 1, (0 : Fin 3) = 0 → i = j
    intro i j _
    exact Subsingleton.elim i j

def tGateApp : GateApp htcxGateSet (1 + 2) :=
  ⟨Gate.ofMatrix1 gateT, Or.inr (Or.inl rfl), tWire⟩

lemma circuit_unitary_singleton {S : Set Gate} {n : ℕ} (g : GateApp S n) :
    Circuit.unitary [g] = embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

lemma circuit_unitary_append {S : Set Gate} {n : ℕ} (c₁ c₂ : Circuit S n) :
    Circuit.unitary (c₁ ++ c₂) = Circuit.unitary c₂ * Circuit.unitary c₁ := by
  simp [Circuit.unitary]

lemma circuit_unitary_replicate {S : Set Gate} {n : ℕ} (g : GateApp S n) (m : ℕ) :
    Circuit.unitary (List.replicate m g) = (embedOp g.gate.mat g.wires) ^ m := by
  induction m with
  | zero => simp [Circuit.unitary]
  | succ m ih =>
    rw [List.replicate_succ', circuit_unitary_append, ih, circuit_unitary_singleton, pow_succ']

lemma embedOp_tGateApp (y z : Qubits (1 + 2)) :
    embedOp tGateApp.gate.mat tGateApp.wires y z =
      if y = z then dT (y 0) else 0 := by
  dsimp [embedOp, tGateApp, Gate.ofMatrix1, gateT, dT, tWire, Matrix.diagonal]
  by_cases hyz : y = z
  · subst hyz
    have : (fun _ : Fin 1 => (0 : Fin (1 + 2))) 0 = 0 := rfl
    simp [this]
  · rw [if_neg hyz]
    split_ifs with h₁ h₂
    · exfalso
      apply hyz
      ext i
      fin_cases i
      · exact h₂
      · apply h₁; rintro ⟨j, hj⟩; revert hj; fin_cases j; decide
      · apply h₁; rintro ⟨j, hj⟩; revert hj; fin_cases j; decide
    · exfalso
      apply hyz
      ext i
      fin_cases i
      · exact h₂
      · apply h₁; rintro ⟨j, hj⟩; revert hj; fin_cases j; decide
      · apply h₁; rintro ⟨j, hj⟩; revert hj; fin_cases j; decide
    · rfl
    · rfl

lemma unitary_tGateApp_replicate (m : ℕ) :
    Circuit.unitary (List.replicate m tGateApp) = Matrix.diagonal (fun y => (dT (y 0)) ^ m) := by
  rw [circuit_unitary_replicate]
  have h : embedOp tGateApp.gate.mat tGateApp.wires = Matrix.diagonal (fun y => dT (y 0)) := by
    ext y z
    rw [embedOp_tGateApp]
    rfl
  rw [h, diagonal_pow]

lemma initializedMap_unitary_append (c₀ : Circuit htcxGateSet (1 + 2)) (m : ℕ)
    (y : Qubits (1 + 2)) (x : Qubits 1) :
    initializedMap (c₀ ++ List.replicate m tGateApp).unitary y x =
      (dT (y 0)) ^ m * initializedMap c₀.unitary y x := by
  dsimp [initializedMap]
  rw [circuit_unitary_append]
  rw [unitary_tGateApp_replicate, diagonal_mul_apply]

lemma oneQubit_gateT :
    oneQubit gateT = Matrix.diagonal (fun u => dT (u 0)) := by
  ext u v
  dsimp [oneQubit, gateT, Matrix.diagonal, dT]
  by_cases huv : u = v
  · subst huv
    simp
  · rw [if_neg huv]
    split_ifs with h₁ h₂
    · exfalso; apply huv; exact qubits1_ext u v h₁
    · exfalso; apply huv; exact qubits1_ext u v h₁
    · rfl

lemma idealMap_red (m : ℕ) (φ' : ℝ) (y : Qubits (1 + 2)) (x : Qubits 1) :
    idealMap (oneQubit gateT ^ m * phaseGate φ') 2 y x =
      (dT (y 0)) ^ m * idealMap (phaseGate φ') 2 y x := by
  dsimp [idealMap]
  rw [oneQubit_gateT, diagonal_pow, diagonal_mul_apply]
  have h0 : (qubitsAppendEquiv 1 2 y).1 0 = y 0 := qubitsAppendEquiv_fst_zero y
  rw [h0]
  split_ifs with h
  · ring
  · ring

lemma frobNorm_eq_of_norm_entry_eq {m n : Type*} [Fintype m] [Fintype n]
    (X Y : Matrix m n ℂ) (h : ∀ i j, ‖X i j‖ = ‖Y i j‖) :
    frobNorm X = frobNorm Y := by
  let : NormedAddCommGroup (Matrix m n ℂ) := Matrix.frobeniusNormedAddCommGroup
  change ‖X‖ = ‖Y‖
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]
  congr 1
  congr 1
  ext i
  congr 1
  ext j
  rw [h i j]

lemma circuit_size_bound (A₀ : ℝ) (k m : ℕ) (c₀_size : ℕ) (hm : m < 8)
    (hc₀ : (c₀_size : ℝ) ≤ A₀ * ((k : ℝ) + 1)) :
    ((c₀_size + m : ℕ) : ℝ) ≤ (A₀ + 7) * ((k : ℝ) + 1) := by
  have hm7 : (m : ℝ) ≤ 7 := by
    have : m ≤ 7 := Nat.lt_succ_iff.mp hm
    exact_mod_cast this
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : ((c₀_size + m : ℕ) : ℝ) = (c₀_size : ℝ) + (m : ℝ) := by push_cast; rfl
  rw [h1]
  have h2 : (c₀_size : ℝ) + (m : ℝ) ≤ A₀ * ((k : ℝ) + 1) + 7 := by linarith
  have h3 : A₀ * ((k : ℝ) + 1) + 7 ≤ (A₀ + 7) * ((k : ℝ) + 1) := by
    calc
      A₀ * ((k : ℝ) + 1) + 7 ≤ A₀ * ((k : ℝ) + 1) + 7 * ((k : ℝ) + 1) := by nlinarith
      _ = (A₀ + 7) * ((k : ℝ) + 1) := by ring
  exact le_trans h2 h3

lemma vecV_has_denom (k : ℕ) (φ : ℝ) (a b c d : ℤ) (z : Qubits 2) :
    ∃ x y : ℤ, vecV k φ a b c d z = ((x : ℂ) + (y : ℂ) * Complex.I) / (2 : ℂ) ^ k := by
  dsimp [vecV, gammaApprox]
  split_ifs
  · exact ⟨c, d, rfl⟩
  · exact ⟨a, b, rfl⟩
  · refine ⟨0, 0, ?_⟩
    simp
  · exact ⟨roundX k φ, roundY k φ, rfl⟩

theorem solution :
    ∃ A : ℝ, 0 < A ∧ ∀ (k : ℕ) (φ : ℝ), ∃ c : Circuit htcxGateSet (1 + 2),
      frobNorm (initializedMap c.unitary - idealMap (phaseGate φ) 2) ≤
        Real.sqrt (2 / 4 ^ k + 2 * Real.sqrt 2 / 2 ^ k) ∧
      (c.size : ℝ) ≤ A * ((k : ℝ) + 1) := by
  rcases CliffordTApprox.Ancilla.controlled_preparation with ⟨A₀, hA₀, hprep⟩
  refine ⟨A₀ + 7, by linarith, fun k φ => ?_⟩
  rcases CliffordTApprox.Ancilla.phase_reduction φ with ⟨m, hm, φ', hφ'₀, hφ'₁, hred⟩
  rcases CliffordTApprox.Ancilla.four_square_unit_vector k φ' hφ'₀ hφ'₁ with ⟨hdef, ⟨a, b, c, d, habcd⟩, hunit⟩
  have hstate : IsState (vecV k φ' a b c d) := hunit a b c d habcd
  have hdenom : ∀ z, ∃ x y : ℤ, vecV k φ' a b c d z = ((x : ℂ) + (y : ℂ) * Complex.I) / (2 : ℂ) ^ k :=
    fun z => vecV_has_denom k φ' a b c d z
  rcases hprep k (vecV k φ' a b c d) hstate hdenom with ⟨c₀, hW, hc₀_size⟩
  have hdist : frobNorm (initializedMap c₀.unitary - idealMap (phaseGate φ') 2) ≤
      Real.sqrt (2 / 4 ^ k + 2 * Real.sqrt 2 / 2 ^ k) :=
    CliffordTApprox.Ancilla.state_distance k φ' hφ'₀ hφ'₁ a b c d habcd c₀.unitary hW
  let c : Circuit htcxGateSet (1 + 2) := c₀ ++ List.replicate m tGateApp
  refine ⟨c, ?_, ?_⟩
  · have hfrob : frobNorm (initializedMap c.unitary - idealMap (phaseGate φ) 2) =
        frobNorm (initializedMap c₀.unitary - idealMap (phaseGate φ') 2) := by
      apply frobNorm_eq_of_norm_entry_eq
      intro y x
      have hinit : initializedMap c.unitary y x = (dT (y 0)) ^ m * initializedMap c₀.unitary y x :=
        initializedMap_unitary_append c₀ m y x
      have hideal : idealMap (phaseGate φ) 2 y x = (dT (y 0)) ^ m * idealMap (phaseGate φ') 2 y x := by
        conv_lhs => rw [hred]
        exact idealMap_red m φ' y x
      rw [Matrix.sub_apply, Matrix.sub_apply, hinit, hideal, ← mul_sub, norm_mul, norm_dT_pow, one_mul]
    rw [hfrob]
    exact hdist
  · have hc_len : c.size = c₀.size + m := by
      change (c₀ ++ List.replicate m tGateApp).length = c₀.length + m
      simp only [List.length_append, List.length_replicate]
    rw [hc_len]
    exact circuit_size_bound A₀ k m c₀.size hm hc₀_size
