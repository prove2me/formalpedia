-- Prove2me | solution 2 for CliffordTApprox.Ancilla.main_result
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-14T03:10:18.905726+00:00
-- url     : https://prove2.me/submissions/5ff7e146-dd88-470d-a6aa-b6764d19e496

import Mathlib
import Definitions.Def_CliffordTApprox_Ancilla_Setting
import Theorems.Thm_CliffordTApprox_Ancilla_decomposition
import Theorems.Thm_CliffordTApprox_Ancilla_composition
import Theorems.Thm_CliffordTApprox_Ancilla_phase_gate_approx

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

private lemma hadamard_mem_unitaryGroup :
    oneQubit hadamard ∈ Matrix.unitaryGroup (Qubits 1) ℂ := by
  refine oneQubit_mem_unitaryGroup ?_
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star hadamard = hadamard := by
    ext a b
    simp only [Matrix.star_apply, hadamard, Matrix.of_apply, Bool.and_comm]
    split_ifs <;> simp
  rw [hstar]
  exact hadamard_mul_self

private def allOk :
    List (Circuit htcxGateSet (1 + 2) × Matrix (Qubits 1) (Qubits 1) ℂ × ℝ) → Prop
  | [] => True
  | x :: rest =>
      (x.2.1 ∈ Matrix.unitaryGroup (Qubits 1) ℂ ∧
        frobNorm (initializedMap x.1.unitary - idealMap x.2.1 2) ≤ x.2.2) ∧
      allOk rest

private lemma compose_chain
    (c₀ : Circuit htcxGateSet (1 + 2)) (U₀ : Matrix (Qubits 1) (Qubits 1) ℂ)
    (hU₀ : U₀ ∈ Matrix.unitaryGroup (Qubits 1) ℂ) (ε₀ : ℝ)
    (h₀ : frobNorm (initializedMap c₀.unitary - idealMap U₀ 2) ≤ ε₀)
    (xs : List (Circuit htcxGateSet (1 + 2) × Matrix (Qubits 1) (Qubits 1) ℂ × ℝ))
    (hxs : allOk xs) :
    ∃ c : Circuit htcxGateSet (1 + 2),
      frobNorm (initializedMap c.unitary -
        idealMap (xs.foldl (fun acc x => x.2.1 * acc) U₀) 2) ≤
        ε₀ + (xs.map (fun x => x.2.2)).sum ∧
      c.size = c₀.size + (xs.map (fun x => x.1.size)).sum := by
  induction xs generalizing c₀ U₀ ε₀ with
  | nil =>
    exact ⟨c₀, by simpa using h₀, by simp⟩
  | cons x rest ih =>
    rcases x with ⟨c₁, U₁, δ₁⟩
    dsimp [allOk] at hxs
    rcases hxs with ⟨hx, hrest⟩
    have hcomp :=
      CliffordTApprox.Ancilla.composition c₀ c₁ U₀ U₁ hU₀ ε₀ δ₁ h₀ hx.2
    have hU' : U₁ * U₀ ∈ Matrix.unitaryGroup (Qubits 1) ℂ :=
      Submonoid.mul_mem _ hx.1 hU₀
    obtain ⟨c, herr, hsize⟩ := ih (c₀ ++ c₁) (U₁ * U₀) hU' (ε₀ + δ₁) hcomp hrest
    refine ⟨c, ?_, ?_⟩
    · simpa [List.foldl_cons, add_assoc] using herr
    · simpa [Circuit.size, List.length_append, add_assoc] using hsize

theorem solution :
    ∃ A : ℝ, 0 < A ∧ ∀ U : Matrix (Qubits 1) (Qubits 1) ℂ,
      U ∈ Matrix.unitaryGroup (Qubits 1) ℂ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ c : Circuit htcxGateSet (1 + 2),
        frobNorm (initializedMap c.unitary - idealMap U 2) ≤ ε ∧
        (c.size : ℝ) ≤ A * (Real.log (1 / ε) / Real.log 2 + 1) := by
  obtain ⟨A₁, hA₁, hphase⟩ := CliffordTApprox.Ancilla.phase_gate_approx
  refine ⟨77 * A₁ + 6, by linarith, fun U hU ε hε₀ hε₁ => ?_⟩
  obtain ⟨θ, φ₁, φ₂, φ₃, hdecomp⟩ := CliffordTApprox.Ancilla.decomposition U hU
  let L : ℝ := Real.log (1 / ε) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1ε : 1 ≤ 1 / ε := (one_le_div hε₀).2 hε₁
  have hL_nonneg : 0 ≤ L := div_nonneg (Real.log_nonneg h1ε) hlog2.le
  let k : ℕ := Nat.ceil (2 * L) + 9
  have hk_ge : 2 * L + 9 ≤ (k : ℝ) := by
    have hceil : 2 * L ≤ (Nat.ceil (2 * L) : ℝ) := Nat.le_ceil (2 * L)
    push_cast [k]
    linarith
  have hk_lt : (k : ℝ) < 2 * L + 10 := by
    have hceil : (Nat.ceil (2 * L) : ℝ) < 2 * L + 1 := Nat.ceil_lt_add_one (by linarith)
    push_cast [k]
    linarith
  have h2k_exp : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h512_exp : 512 / ε ^ 2 = Real.exp ((2 * L + 9) * Real.log 2) := by
    have hexp1 : Real.exp (2 * L * Real.log 2) = (1 / ε) ^ 2 := by
      have harg : 2 * L * Real.log 2 = (2 : ℕ) * Real.log (1 / ε) := by
        dsimp [L]
        field_simp [hlog2.ne']
      rw [harg, Real.exp_nat_mul, Real.exp_log (by positivity)]
    have hexp2 : Real.exp (9 * Real.log 2) = 512 := by
      have harg : (9 : ℝ) * Real.log 2 = (9 : ℕ) * Real.log 2 := by norm_num
      rw [harg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
      norm_num
    rw [add_mul, Real.exp_add, hexp1, hexp2]
    ring
  have h2k_ge : 512 / ε ^ 2 ≤ (2 : ℝ) ^ k := by
    rw [h512_exp, h2k_exp]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hk_ge hlog2.le)
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h2k_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have h4k_ge : (2 : ℝ) ^ k ≤ (4 : ℝ) ^ k := by
    have h4 : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4]
    nlinarith
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have herr_rad : 2 / (4 : ℝ) ^ k + 2 * Real.sqrt 2 / (2 : ℝ) ^ k ≤ (ε / 7) ^ 2 := by
    have h1 : 2 / (4 : ℝ) ^ k ≤ 2 / (2 : ℝ) ^ k :=
      div_le_div_of_nonneg_left (by norm_num) h2k_pos h4k_ge
    have h2 : 2 * Real.sqrt 2 / (2 : ℝ) ^ k ≤ 3 / (2 : ℝ) ^ k :=
      div_le_div_of_nonneg_right (by linarith) h2k_pos.le
    have h3 : 5 / (2 : ℝ) ^ k ≤ 5 / (512 / ε ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) h2k_ge
    have h4 : 5 / (512 / ε ^ 2) = 5 / 512 * ε ^ 2 := by field_simp
    have h5 : 5 / 512 * ε ^ 2 ≤ (ε / 7) ^ 2 := by nlinarith [sq_nonneg ε]
    calc 2 / (4 : ℝ) ^ k + 2 * Real.sqrt 2 / (2 : ℝ) ^ k
        ≤ 2 / (2 : ℝ) ^ k + 3 / (2 : ℝ) ^ k := add_le_add h1 h2
      _ = 5 / (2 : ℝ) ^ k := by ring
      _ ≤ 5 / (512 / ε ^ 2) := h3
      _ = 5 / 512 * ε ^ 2 := h4
      _ ≤ (ε / 7) ^ 2 := h5
  have herr_phase : Real.sqrt (2 / (4 : ℝ) ^ k + 2 * Real.sqrt 2 / (2 : ℝ) ^ k) ≤ ε / 7 := by
    calc Real.sqrt (2 / (4 : ℝ) ^ k + 2 * Real.sqrt 2 / (2 : ℝ) ^ k)
        ≤ Real.sqrt ((ε / 7) ^ 2) := Real.sqrt_le_sqrt herr_rad
      _ = ε / 7 := Real.sqrt_sq (by positivity)
  obtain ⟨cθ, hcθ_err, hcθ_size⟩ := hphase k θ
  obtain ⟨cπ, hcπ_err, hcπ_size⟩ := hphase k Real.pi
  obtain ⟨cφ₁, hcφ₁_err, hcφ₁_size⟩ := hphase k φ₁
  obtain ⟨cφ₂, hcφ₂_err, hcφ₂_size⟩ := hphase k φ₂
  obtain ⟨cφ₃, hcφ₃_err, hcφ₃_size⟩ := hphase k φ₃
  let gH : GateApp htcxGateSet (1 + 2) :=
    ⟨Gate.ofMatrix1 hadamard, by simp [htcxGateSet], wire0⟩
  let cH : Circuit htcxGateSet (1 + 2) := [gH]
  have hcH_unitary : cH.unitary = liftData (oneQubit hadamard) := by
    change (List.map (fun g => embedOp g.gate.mat g.wires) [gH]).reverse.prod = _
    simp [gH, embedOp_wire0]
  have hcH_err : frobNorm (initializedMap cH.unitary - idealMap (oneQubit hadamard) 2) ≤ 0 := by
    rw [hcH_unitary, initializedMap_liftData, sub_self, frobNorm]
    let _ : NormedAddCommGroup (Matrix (Qubits (1 + 2)) (Qubits 1) ℂ) :=
      Matrix.frobeniusNormedAddCommGroup
    exact le_of_eq norm_zero
  have hcH_size : cH.size = 1 := rfl
  let xs : List (Circuit htcxGateSet (1 + 2) × Matrix (Qubits 1) (Qubits 1) ℂ × ℝ) :=
    [ (cH, oneQubit hadamard, 0),
      (cφ₂, phaseGate φ₂, ε / 7),
      (cH, oneQubit hadamard, 0),
      (cφ₁, phaseGate φ₁, ε / 7),
      (cH, oneQubit hadamard, 0),
      (cπ, phaseGate Real.pi, ε / 7),
      (cH, oneQubit hadamard, 0),
      (cθ, phaseGate θ, ε / 7),
      (cH, oneQubit hadamard, 0),
      (cπ, phaseGate Real.pi, ε / 7),
      (cH, oneQubit hadamard, 0),
      (cθ, phaseGate θ, ε / 7) ]
  have hH_ok : oneQubit hadamard ∈ Matrix.unitaryGroup (Qubits 1) ℂ ∧
      frobNorm (initializedMap cH.unitary - idealMap (oneQubit hadamard) 2) ≤ 0 :=
    ⟨hadamard_mem_unitaryGroup, hcH_err⟩
  have hP_ok (α : ℝ) (cα : Circuit htcxGateSet (1 + 2))
      (hcα : frobNorm (initializedMap cα.unitary - idealMap (phaseGate α) 2) ≤
        Real.sqrt (2 / 4 ^ k + 2 * Real.sqrt 2 / 2 ^ k)) :
      phaseGate α ∈ Matrix.unitaryGroup (Qubits 1) ℂ ∧
      frobNorm (initializedMap cα.unitary - idealMap (phaseGate α) 2) ≤ ε / 7 :=
    ⟨phaseGate_mem_unitaryGroup α, hcα.trans herr_phase⟩
  have hxs : allOk xs := by
    dsimp [xs, allOk]
    exact ⟨hH_ok, hP_ok φ₂ cφ₂ hcφ₂_err, hH_ok, hP_ok φ₁ cφ₁ hcφ₁_err,
      hH_ok, hP_ok Real.pi cπ hcπ_err, hH_ok, hP_ok θ cθ hcθ_err,
      hH_ok, hP_ok Real.pi cπ hcπ_err, hH_ok, hP_ok θ cθ hcθ_err, trivial⟩
  obtain ⟨c, hc_err, hc_size⟩ :=
    compose_chain cφ₃ (phaseGate φ₃) (phaseGate_mem_unitaryGroup φ₃) (ε / 7)
      (hcφ₃_err.trans herr_phase) xs hxs
  have hfold : xs.foldl (fun acc x => x.2.1 * acc) (phaseGate φ₃) = U := by
    rw [hdecomp]
    simp [xs, mul_assoc]
  rw [hfold] at hc_err
  refine ⟨c, ?_, ?_⟩
  · have hsum_err : ε / 7 + (xs.map (fun x => x.2.2)).sum = ε := by
      simp [xs]
      ring
    linarith only [hc_err, hsum_err]
  · have hsum_size : (c.size : ℝ) =
        (cφ₃.size : ℝ) + (cφ₂.size : ℝ) + (cφ₁.size : ℝ) +
          (cπ.size : ℝ) + (cθ.size : ℝ) + (cπ.size : ℝ) + (cθ.size : ℝ) + 6 := by
      rw [hc_size]
      simp [xs, hcH_size]
      ring
    have hk1_le : (k : ℝ) + 1 ≤ 11 * (L + 1) := by linarith only [hk_lt, hL_nonneg]
    have h1_le : (1 : ℝ) ≤ L + 1 := by linarith only [hL_nonneg]
    calc (c.size : ℝ)
        = (cφ₃.size : ℝ) + (cφ₂.size : ℝ) + (cφ₁.size : ℝ) +
            (cπ.size : ℝ) + (cθ.size : ℝ) + (cπ.size : ℝ) + (cθ.size : ℝ) + 6 := hsum_size
      _ ≤ 7 * (A₁ * ((k : ℝ) + 1)) + 6 := by
          linarith only [hcφ₃_size, hcφ₂_size, hcφ₁_size, hcπ_size, hcθ_size]
      _ ≤ 7 * (A₁ * (11 * (L + 1))) + 6 * (L + 1) := by
          nlinarith only [hA₁, hk1_le, h1_le]
      _ = (77 * A₁ + 6) * (L + 1) := by ring
