-- Prove2me | solution 2 for CliffordTApprox.Ancilla.phase_gate_approx
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-14T03:08:23.507165+00:00
-- url     : https://prove2.me/submissions/f261ca11-90dd-4cc2-a52d-0c5f6b6e4e00

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting
import Theorems.Thm_CliffordTApprox_Ancilla_phase_reduction
import Theorems.Thm_CliffordTApprox_Ancilla_four_square_unit_vector
import Theorems.Thm_CliffordTApprox_Ancilla_state_distance
import Theorems.Thm_CliffordTApprox_Ancilla_composition
import Theorems.Thm_CliffordTApprox_Ancilla_controlled_preparation

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12
open CliffordTApprox.Ancilla

private def wire0 : Fin 1 ↪ Fin (1 + 2) :=
  ⟨fun _ => 0, fun x y _ => Subsingleton.elim x y⟩

private def liftData (U : Matrix (Qubits 1) (Qubits 1) ℂ) :
    Matrix (Qubits (1 + 2)) (Qubits (1 + 2)) ℂ :=
  Matrix.of fun y z =>
    if (qubitsAppendEquiv 1 2 y).2 = (qubitsAppendEquiv 1 2 z).2 then
      U (qubitsAppendEquiv 1 2 y).1 (qubitsAppendEquiv 1 2 z).1
    else 0

private lemma liftData_one : liftData 1 = 1 := by
  ext y z
  simp only [liftData, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso
      apply hyz
      apply (qubitsAppendEquiv 1 2).injective
      exact Prod.ext h2 h1
    · rfl
    · rfl

private lemma liftData_mul (A B : Matrix (Qubits 1) (Qubits 1) ℂ) :
    liftData (A * B) = liftData A * liftData B := by
  ext y z
  simp only [liftData, Matrix.of_apply, Matrix.mul_apply]
  rw [← (qubitsAppendEquiv 1 2).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  by_cases h2 : (qubitsAppendEquiv 1 2 y).2 = (qubitsAppendEquiv 1 2 z).2
  · rw [if_pos h2]
    refine Finset.sum_congr rfl fun w1 _ => ?_
    rw [Finset.sum_eq_single (qubitsAppendEquiv 1 2 y).2]
    · simp [h2]
    · intro w2 _ hw2
      have hne : (qubitsAppendEquiv 1 2 y).2 ≠ w2 := hw2.symm
      simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [if_neg h2]
    refine (Finset.sum_eq_zero fun w1 _ => ?_).symm
    refine Finset.sum_eq_zero fun w2 _ => ?_
    by_cases hw2 : (qubitsAppendEquiv 1 2 y).2 = w2
    · have hne : w2 ≠ (qubitsAppendEquiv 1 2 z).2 := fun h => h2 (hw2.trans h)
      simp [hw2, hne]
    · simp [hw2]

private lemma liftData_pow (A : Matrix (Qubits 1) (Qubits 1) ℂ) (m : ℕ) :
    liftData (A ^ m) = liftData A ^ m := by
  induction m with
  | zero => simp [liftData_one]
  | succ m ih => rw [pow_succ, pow_succ, liftData_mul, ih]

private lemma embedOp_wire0 (M : Matrix Bool Bool ℂ) :
    embedOp (Gate.ofMatrix1 M).mat wire0 = liftData (oneQubit M) := by
  ext y z
  have hcond :
      (∀ a : Fin (1 + 2), a ∉ Set.range wire0 → y a = z a) ↔
        (qubitsAppendEquiv 1 2 y).2 = (qubitsAppendEquiv 1 2 z).2 := by
    constructor
    · intro h
      funext j
      apply h (Fin.natAdd 1 j)
      rintro ⟨_, hj⟩
      have hjv := congrArg Fin.val hj
      change (0 : ℕ) = 1 + (j : ℕ) at hjv
      omega
    · intro h a ha
      have ha0 : a ≠ 0 := fun h0 => ha ⟨0, h0.symm⟩
      have ha_pos : 0 < a.1 := Nat.pos_of_ne_zero (fun h0 => ha0 (Fin.ext h0))
      have hj : ∃ j : Fin 2, a = Fin.natAdd 1 j :=
        ⟨⟨a.1 - 1, by omega⟩, Fin.ext (by simp [Fin.natAdd]; omega)⟩
      obtain ⟨j, rfl⟩ := hj
      exact congrFun h j
  dsimp [embedOp, liftData, Gate.ofMatrix1, oneQubit]
  by_cases h2 : (qubitsAppendEquiv 1 2 y).2 = (qubitsAppendEquiv 1 2 z).2
  · rw [if_pos (hcond.2 h2), if_pos h2]
    rfl
  · rw [if_neg (mt hcond.1 h2), if_neg h2]

private lemma initializedMap_liftData (U : Matrix (Qubits 1) (Qubits 1) ℂ) :
    initializedMap (liftData U) = idealMap U 2 := by
  ext y x
  simp only [initializedMap, liftData, idealMap, Matrix.of_apply]
  have happ : qubitsAppendEquiv 1 2 (Fin.append x (fun _ : Fin 2 => false)) = (x, fun _ => false) :=
    (qubitsAppendEquiv 1 2).apply_symm_apply (x, fun _ => false)
  rw [happ]

private def qubits1EquivBool : Qubits 1 ≃ Bool where
  toFun b := b 0
  invFun a _ := a
  left_inv b := funext fun i => by fin_cases i; rfl
  right_inv _ := rfl

private lemma oneQubit_mem_unitaryGroup {M : Matrix Bool Bool ℂ}
    (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    oneQubit M ∈ Matrix.unitaryGroup (Qubits 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  ext x y
  have hmul : (oneQubit M * star (oneQubit M)) x y = (M * star M) (x 0) (y 0) := by
    simp only [Matrix.mul_apply, Matrix.star_apply, oneQubit, Matrix.submatrix_apply]
    exact Fintype.sum_equiv qubits1EquivBool _ _ (fun _ => rfl)
  rw [hmul, hM, Matrix.one_apply, Matrix.one_apply]
  have hxy : x 0 = y 0 ↔ x = y := qubits1EquivBool.injective.eq_iff
  simp [hxy]

private lemma phaseGate_mem_unitaryGroup (φ : ℝ) :
    phaseGate φ ∈ Matrix.unitaryGroup (Qubits 1) ℂ := by
  refine oneQubit_mem_unitaryGroup ?_
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  cases a <;> cases b <;> simp [Matrix.mul_apply, Matrix.star_apply]
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    mul_neg, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem solution :
    ∃ A : ℝ, 0 < A ∧ ∀ (k : ℕ) (φ : ℝ), ∃ c : Circuit htcxGateSet (1 + 2),
      frobNorm (initializedMap c.unitary - idealMap (phaseGate φ) 2) ≤
        Real.sqrt (2 / 4 ^ k + 2 * Real.sqrt 2 / 2 ^ k) ∧
      (c.size : ℝ) ≤ A * ((k : ℝ) + 1) := by
  obtain ⟨A₀, hA₀, hprep⟩ := CliffordTApprox.Ancilla.controlled_preparation
  refine ⟨A₀ + 7, by linarith, fun k φ => ?_⟩
  obtain ⟨m, hm, φ', hφ'₀, hφ'₁, hphase⟩ := CliffordTApprox.Ancilla.phase_reduction φ
  obtain ⟨_, ⟨a, b, c, d, habcd⟩, hv_state⟩ :=
    CliffordTApprox.Ancilla.four_square_unit_vector k φ' hφ'₀ hφ'₁
  have hv : IsState (vecV k φ' a b c d) := hv_state a b c d habcd
  have hv_denom : ∀ z : Qubits 2,
      ∃ x y : ℤ, vecV k φ' a b c d z = ((x : ℂ) + (y : ℂ) * Complex.I) / (2 : ℂ) ^ k := by
    intro z
    cases hz0 : z 0 <;> cases hz1 : z 1
    · exact ⟨roundX k φ', roundY k φ', by simp [vecV, hz0, hz1, gammaApprox]⟩
    · exact ⟨0, 0, by simp [vecV, hz0, hz1]⟩
    · exact ⟨a, b, by simp [vecV, hz0, hz1]⟩
    · exact ⟨c, d, by simp [vecV, hz0, hz1]⟩
  obtain ⟨c₁, hc₁_prep, hc₁_size⟩ := hprep k (vecV k φ' a b c d) hv hv_denom
  have hdist₁ :=
    CliffordTApprox.Ancilla.state_distance k φ' hφ'₀ hφ'₁ a b c d habcd c₁.unitary hc₁_prep
  let gT : GateApp htcxGateSet (1 + 2) :=
    ⟨Gate.ofMatrix1 gateT, by simp [htcxGateSet], wire0⟩
  let c₂ : Circuit htcxGateSet (1 + 2) := List.replicate m gT
  have hc₂_unitary : c₂.unitary = liftData (oneQubit gateT ^ m) := by
    change (List.map (fun g => embedOp g.gate.mat g.wires) (List.replicate m gT)).reverse.prod = _
    rw [List.map_replicate, List.reverse_replicate, List.prod_replicate, liftData_pow]
    congr 1
    exact embedOp_wire0 gateT
  have hc₂_init : initializedMap c₂.unitary = idealMap (oneQubit gateT ^ m) 2 := by
    rw [hc₂_unitary, initializedMap_liftData]
  have hdist₂ :
      frobNorm (initializedMap c₂.unitary - idealMap (oneQubit gateT ^ m) 2) ≤ 0 := by
    rw [hc₂_init, sub_self, frobNorm]
    let _ : NormedAddCommGroup (Matrix (Qubits (1 + 2)) (Qubits 1) ℂ) :=
      Matrix.frobeniusNormedAddCommGroup
    exact le_of_eq norm_zero
  have hcomp :=
    CliffordTApprox.Ancilla.composition c₁ c₂ (phaseGate φ') (oneQubit gateT ^ m)
      (phaseGate_mem_unitaryGroup φ') _ 0 hdist₁ hdist₂
  rw [add_zero, ← hphase] at hcomp
  refine ⟨c₁ ++ c₂, hcomp, ?_⟩
  have hc₂_size : c₂.size = m := List.length_replicate
  have hm_le : (m : ℝ) ≤ 7 := by exact_mod_cast Nat.le_of_lt_succ hm
  have hk_nonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc ((c₁ ++ c₂).size : ℝ)
      = (c₁.size : ℝ) + (c₂.size : ℝ) := by simp [Circuit.size]
    _ = (c₁.size : ℝ) + (m : ℝ) := by rw [hc₂_size]
    _ ≤ A₀ * ((k : ℝ) + 1) + 7 := add_le_add hc₁_size hm_le
    _ ≤ A₀ * ((k : ℝ) + 1) + 7 * ((k : ℝ) + 1) := by nlinarith
    _ = (A₀ + 7) * ((k : ℝ) + 1) := by ring
