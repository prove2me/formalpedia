-- Prove2me | solution 1 for CliffordTApprox.Ancilla.main_result
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:15:49.392999+00:00
-- url     : https://prove2.me/submissions/dd53c067-7876-4ee4-8e65-0b19c237bf7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CliffordTApprox_Ancilla_Setting
import Theorems.Thm_CliffordTApprox_Ancilla_decomposition
import Theorems.Thm_CliffordTApprox_Ancilla_phase_gate_approx
import Theorems.Thm_CliffordTApprox_Ancilla_composition

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12
open CliffordTApprox.Ancilla

def hWire : Fin 1 ↪ Fin (1 + 2) where
  toFun _ := 0
  inj' i j _ := Subsingleton.elim i j

noncomputable def gH : GateApp htcxGateSet (1 + 2) :=
  ⟨Gate.ofMatrix1 hadamard, Or.inl rfl, hWire⟩

lemma cH_unitary :
    Circuit.unitary [gH] = embedOp (Gate.ofMatrix1 hadamard).mat hWire := by
  change (embedOp (Gate.ofMatrix1 hadamard).mat hWire) * 1 = _
  exact mul_one _

lemma cond_equiv (y : Qubits (1 + 2)) (x : Qubits 1) :
    (∀ a ∉ Set.range ⇑hWire, y a = Fin.append x (fun _ => false) a) ↔
    (((qubitsAppendEquiv 1 2) y).2 = fun _ => false) := by
  change _ ↔ ((fun j => y (Fin.natAdd 1 j)) = fun _ => false)
  constructor
  · intro h
    ext j
    fin_cases j
    · have hnot : (1 : Fin 3) ∉ Set.range ⇑hWire := by
        rintro ⟨k, hk⟩
        fin_cases k
        revert hk
        decide
      have := h 1 hnot
      exact this
    · have hnot : (2 : Fin 3) ∉ Set.range ⇑hWire := by
        rintro ⟨k, hk⟩
        fin_cases k
        revert hk
        decide
      have := h 2 hnot
      exact this
  · intro h a ha
    fin_cases a
    · exfalso
      apply ha
      exact ⟨0, rfl⟩
    · have : (fun j => y (Fin.natAdd 1 j)) 0 = false := by rw [h]
      exact this
    · have : (fun j => y (Fin.natAdd 1 j)) 1 = false := by rw [h]
      exact this

lemma cH_ideal :
    initializedMap (Circuit.unitary [gH]) = idealMap (oneQubit hadamard) 2 := by
  rw [cH_unitary]
  ext y x
  dsimp [initializedMap, idealMap, embedOp, Gate.ofMatrix1, oneQubit]
  have heq := cond_equiv y x
  by_cases h : ((qubitsAppendEquiv 1 2) y).2 = fun _ => false
  · have h1 : ∀ a ∉ Set.range ⇑hWire, y a = Fin.append x (fun _ => false) a := heq.mpr h
    rw [if_pos h1, if_pos h]
    rfl
  · have h1 : ¬∀ a ∉ Set.range ⇑hWire, y a = Fin.append x (fun _ => false) a := fun h' => h (heq.mp h')
    rw [if_neg h1, if_neg h]

lemma cH_frobNorm :
    frobNorm (initializedMap (Circuit.unitary [gH]) - idealMap (oneQubit hadamard) 2) ≤ 0 := by
  rw [cH_ideal, sub_self]
  let _ : NormedAddCommGroup (Matrix (Qubits (1 + 2)) (Qubits 1) ℂ) := Matrix.frobeniusNormedAddCommGroup
  change ‖(0 : Matrix (Qubits (1 + 2)) (Qubits 1) ℂ)‖ ≤ 0
  simp

lemma star_sqrt2_inv : (starRingEnd ℂ) ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  have : (starRingEnd ℂ) ((Real.sqrt 2)⁻¹ : ℂ) = star ((Real.sqrt 2)⁻¹ : ℂ) := rfl
  rw [this, Complex.star_def, ← Complex.ofReal_inv, Complex.conj_ofReal, Complex.ofReal_inv]

lemma hsq : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; rfl
  have hinv : ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ = (2 : ℂ)⁻¹ := by rw [h2]
  rw [← mul_inv, hinv]
  norm_num

lemma qubits1_univ : (Finset.univ : Finset (Qubits 1)) = {fun _ => false, fun _ => true} := by
  ext x
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  have : x 0 = false ∨ x 0 = true := Bool.casesOn (x 0) (Or.inl rfl) (Or.inr rfl)
  rcases this with h | h
  · left; ext k; have : k = 0 := Subsingleton.elim k 0; rw [this, h]
  · right; ext k; have : k = 0 := Subsingleton.elim k 0; rw [this, h]

lemma qubits1_sum (f : Qubits 1 → ℂ) :
    (∑ x : Qubits 1, f x) = f (fun _ => false) + f (fun _ => true) := by
  have hne : (fun _ : Fin 1 => false) ∉ ({fun _ : Fin 1 => true} : Finset (Qubits 1)) := by
    simp only [Finset.mem_singleton]
    intro h
    have := congr_fun h 0
    revert this
    decide
  change ∑ x ∈ Finset.univ, f x = _
  rw [qubits1_univ, Finset.sum_insert hne, Finset.sum_singleton]

lemma hadamard_unitary_aux : oneQubit hadamard ∈ Matrix.unitaryGroup (Qubits 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have heq : (i = j) ↔ (i 0 = j 0) := ⟨fun h => by rw [h], fun h => by ext k; have : k = 0 := Subsingleton.elim k 0; rw [this, h]⟩
  have hi : i 0 = false ∨ i 0 = true := Bool.casesOn (i 0) (Or.inl rfl) (Or.inr rfl)
  have hj : j 0 = false ∨ j 0 = true := Bool.casesOn (j 0) (Or.inl rfl) (Or.inr rfl)
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
  simp only [oneQubit, hadamard, Matrix.mul_apply, Matrix.of_apply, Matrix.submatrix_apply,
    Matrix.one_apply, Matrix.star_apply, hi, hj, heq, if_true, Bool.false_and, Bool.true_and] <;>
  rw [qubits1_sum] <;>
  dsimp <;>
  simp only [star_sqrt2_inv, map_neg] <;>
  try ring_nf <;>
  linear_combination 2 * hsq

lemma oneQubit_diagonal (d : Bool → ℂ) :
    oneQubit (Matrix.diagonal d) = Matrix.diagonal (fun (b : Qubits 1) => d (b 0)) := by
  ext x y
  simp only [oneQubit, Matrix.submatrix_apply, Matrix.diagonal_apply]
  have heq : (x = y) ↔ (x 0 = y 0) := ⟨fun h => by rw [h], fun h => by ext k; have : k = 0 := Subsingleton.elim k 0; rw [this, h]⟩
  by_cases h : x 0 = y 0
  · rw [if_pos h, if_pos (heq.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (heq.mp h'))]

lemma phaseGate_unitary (φ : ℝ) : phaseGate φ ∈ Matrix.unitaryGroup (Qubits 1) ℂ := by
  rw [phaseGate, oneQubit_diagonal]
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : star (Matrix.diagonal fun (b : Qubits 1) => if b 0 = true then Complex.exp (↑φ * Complex.I) else 1) =
      Matrix.diagonal (star fun (b : Qubits 1) => if b 0 = true then Complex.exp (↑φ * Complex.I) else 1) := by
    exact Matrix.diagonal_conjTranspose _
  rw [hs, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  ext b
  dsimp [star]
  split_ifs with hb
  · have hc : (starRingEnd ℂ) (Complex.exp (↑φ * Complex.I)) = Complex.exp (starRingEnd ℂ (↑φ * Complex.I)) := by
      exact (Complex.exp_conj _).symm
    rw [hc]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [← Complex.exp_add]
    have hsum : (↑φ : ℂ) * Complex.I + ↑φ * -Complex.I = 0 := by ring
    rw [hsum, Complex.exp_zero]
  · simp

lemma pow_ceil_bound (ε : ℝ) (hε : 0 < ε) :
    let n := ⌈Real.log (1 / ε) / Real.log 2⌉₊
    1 / (2 : ℝ) ^ n ≤ ε := by
  intro n
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hle : Real.log (1 / ε) / Real.log 2 ≤ (n : ℝ) := Nat.le_ceil _
  have hmul : Real.log (1 / ε) ≤ (n : ℝ) * Real.log 2 := (div_le_iff₀ hlog2).mp hle
  rw [← Real.log_pow] at hmul
  have hpow_pos : 0 < (2 : ℝ) ^ n := by positivity
  have hle' : 1 / ε ≤ (2 : ℝ) ^ n := (Real.log_le_log_iff hinv_pos hpow_pos).mp hmul
  rw [one_div_le hpow_pos hε]
  exact hle'

lemma sqrt2_le : 2 * Real.sqrt 2 ≤ 3 := by
  have : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  linarith

lemma k_bound (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hn : 1 / (2 : ℝ) ^ n ≤ ε) :
    let k := 2 * n + 8
    7 * Real.sqrt (2 / 4 ^ k + 2 * Real.sqrt 2 / 2 ^ k) ≤ ε := by
  intro k
  have h2k_pos : 0 < (2 : ℝ) ^ k := by positivity
  have h2_le_4 : (2 : ℝ) ^ k ≤ (4 : ℝ) ^ k := by
    gcongr
    norm_num
  have hterm1 : (2 : ℝ) / 4 ^ k ≤ 2 / 2 ^ k := by
    exact div_le_div_of_nonneg_left (by norm_num) h2k_pos h2_le_4
  have hterm2 : 2 * Real.sqrt 2 / (2 : ℝ) ^ k ≤ 3 / (2 : ℝ) ^ k := by
    exact div_le_div_of_nonneg_right sqrt2_le (le_of_lt h2k_pos)
  have hsum : 2 / (4 : ℝ) ^ k + 2 * Real.sqrt 2 / (2 : ℝ) ^ k ≤ 5 / (2 : ℝ) ^ k := by
    have : (2 : ℝ) / 2 ^ k + 3 / 2 ^ k = 5 / 2 ^ k := by ring
    linarith [hterm1, hterm2]
  have hpow_split : (2 : ℝ) ^ k = 256 * ((2 : ℝ) ^ n) ^ 2 := by
    dsimp [k]
    have : 2 * n + 8 = 8 + n * 2 := by omega
    rw [this, pow_add, pow_mul]
    norm_num
  have h5_256 : (5 : ℝ) / (2 : ℝ) ^ k ≤ (1 / 49) * (1 / (2 : ℝ) ^ n) ^ 2 := by
    rw [hpow_split]
    have : (1 : ℝ) / ((2 : ℝ) ^ n) ^ 2 = ((1 : ℝ) / (2 : ℝ) ^ n) ^ 2 := by ring
    rw [← this]
    rw [div_mul_eq_div_mul_one_div]
    have : (5 : ℝ) / 256 ≤ 1 / 49 := by norm_num
    have hpos : 0 ≤ (1 : ℝ) / ((2 : ℝ) ^ n) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right this hpos
  have hsq_le : (1 / (2 : ℝ) ^ n) ^ 2 ≤ ε ^ 2 := by
    have hpos : 0 ≤ 1 / (2 : ℝ) ^ n := by positivity
    exact sq_le_sq.mpr (by rw [abs_of_nonneg hpos, abs_of_pos hε]; exact hn)
  have h5_eps : (5 : ℝ) / (2 : ℝ) ^ k ≤ (1 / 49) * ε ^ 2 := by
    linarith [mul_le_mul_of_nonneg_left hsq_le (by norm_num : (0 : ℝ) ≤ 1 / 49)]
  have hinner : 2 / (4 : ℝ) ^ k + 2 * Real.sqrt 2 / (2 : ℝ) ^ k ≤ (ε / 7) ^ 2 := by
    have : (ε / 7) ^ 2 = (1 / 49) * ε ^ 2 := by ring
    linarith
  have hinner_nonneg : 0 ≤ 2 / (4 : ℝ) ^ k + 2 * Real.sqrt 2 / (2 : ℝ) ^ k := by positivity
  have hsqrt := Real.sqrt_le_sqrt hinner
  rw [Real.sqrt_sq (by positivity)] at hsqrt
  linarith

lemma size_bound (A₀ : ℝ) (hA₀ : 0 < A₀) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let n := ⌈Real.log (1 / ε) / Real.log 2⌉₊
    let k := 2 * n + 8
    7 * (A₀ * ((k : ℝ) + 1)) + 6 ≤ (77 * A₀ + 6) * (Real.log (1 / ε) / Real.log 2 + 1) := by
  intro n k
  set L := Real.log (1 / ε) / Real.log 2 + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_eps : 0 ≤ Real.log (1 / ε) := by
    rw [← Real.log_one]
    apply Real.log_le_log (by norm_num)
    exact one_le_one_div hε hε1
  have hdiv_nonneg : 0 ≤ Real.log (1 / ε) / Real.log 2 := div_nonneg hlog_eps (le_of_lt hlog2)
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith
  have hn_le : (n : ℝ) ≤ Real.log (1 / ε) / Real.log 2 + 1 := le_of_lt (Nat.ceil_lt_add_one hdiv_nonneg)
  have hk_le : (k : ℝ) + 1 ≤ 11 * L := by
    dsimp [k]
    push_cast
    have : (2 : ℝ) * (n : ℝ) + 8 + 1 = 2 * (n : ℝ) + 9 := by ring
    rw [this]
    dsimp [L]
    linarith
  have : 7 * (A₀ * ((k : ℝ) + 1)) + 6 ≤ 7 * (A₀ * (11 * L)) + 6 * L := by
    nlinarith
  have : 7 * (A₀ * (11 * L)) + 6 * L = (77 * A₀ + 6) * L := by ring
  linarith

theorem solution :
    ∃ A : ℝ, 0 < A ∧ ∀ U : Matrix (Qubits 1) (Qubits 1) ℂ,
      U ∈ Matrix.unitaryGroup (Qubits 1) ℂ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ c : Circuit htcxGateSet (1 + 2),
        frobNorm (initializedMap c.unitary - idealMap U 2) ≤ ε ∧
        (c.size : ℝ) ≤ A * (Real.log (1 / ε) / Real.log 2 + 1) := by
  obtain ⟨A₀, hA₀_pos, h_phase⟩ := phase_gate_approx
  use 77 * A₀ + 6
  refine ⟨by linarith, ?_⟩
  intro U hU ε hε hε1
  obtain ⟨θ, φ₁, φ₂, φ₃, hU_dec⟩ := decomposition U hU
  set n := ⌈Real.log (1 / ε) / Real.log 2⌉₊
  set k := 2 * n + 8
  set δ := Real.sqrt (2 / 4 ^ k + 2 * Real.sqrt 2 / 2 ^ k)
  obtain ⟨c_θ, hc_θ_err, hc_θ_sz⟩ := h_phase k θ
  obtain ⟨c_pi, hc_pi_err, hc_pi_sz⟩ := h_phase k Real.pi
  obtain ⟨c_φ₁, hc_φ₁_err, hc_φ₁_sz⟩ := h_phase k φ₁
  obtain ⟨c_φ₂, hc_φ₂_err, hc_φ₂_sz⟩ := h_phase k φ₂
  obtain ⟨c_φ₃, hc_φ₃_err, hc_φ₃_sz⟩ := h_phase k φ₃
  set c_H : Circuit htcxGateSet (1 + 2) := [gH]
  have hc_H_err : frobNorm (initializedMap c_H.unitary - idealMap (oneQubit hadamard) 2) ≤ 0 := cH_frobNorm
  set X := oneQubit hadamard * phaseGate Real.pi * oneQubit hadamard
  have hX_u : X ∈ Matrix.unitaryGroup (Qubits 1) ℂ :=
    mul_mem (mul_mem hadamard_unitary_aux (phaseGate_unitary Real.pi)) hadamard_unitary_aux
  set c_pi_H : Circuit htcxGateSet (1 + 2) := c_pi ++ c_H
  have hc_pi_H_err : frobNorm (initializedMap c_pi_H.unitary - idealMap (oneQubit hadamard * phaseGate Real.pi) 2) ≤ δ := by
    have h := composition c_pi c_H (phaseGate Real.pi) (oneQubit hadamard) (phaseGate_unitary Real.pi) δ 0 hc_pi_err hc_H_err
    linarith
  set cX : Circuit htcxGateSet (1 + 2) := c_H ++ c_pi_H
  have hcX_err : frobNorm (initializedMap cX.unitary - idealMap X 2) ≤ δ := by
    have h := composition c_H c_pi_H (oneQubit hadamard) (oneQubit hadamard * phaseGate Real.pi) hadamard_unitary_aux 0 δ hc_H_err hc_pi_H_err
    linarith
  set c₀ := c_θ
  have hc₀_err : frobNorm (initializedMap c₀.unitary - idealMap (phaseGate θ) 2) ≤ δ := hc_θ_err
  set c₁ := cX ++ c₀
  have hc₁_err : frobNorm (initializedMap c₁.unitary - idealMap (phaseGate θ * X) 2) ≤ 2 * δ := by
    have h := composition cX c₀ X (phaseGate θ) hX_u δ δ hcX_err hc₀_err
    linarith
  set c₂ := c_θ ++ c₁
  have hc₂_err : frobNorm (initializedMap c₂.unitary - idealMap (phaseGate θ * X * phaseGate θ) 2) ≤ 3 * δ := by
    have h := composition c_θ c₁ (phaseGate θ) (phaseGate θ * X) (phaseGate_unitary θ) δ (2 * δ) hc_θ_err hc₁_err
    linarith
  set c₃ := cX ++ c₂
  have hc₃_err : frobNorm (initializedMap c₃.unitary - idealMap (phaseGate θ * X * phaseGate θ * X) 2) ≤ 4 * δ := by
    have h := composition cX c₂ X (phaseGate θ * X * phaseGate θ) hX_u δ (3 * δ) hcX_err hc₂_err
    linarith
  set c₄ := c_φ₁ ++ c₃
  have hc₄_err : frobNorm (initializedMap c₄.unitary - idealMap (phaseGate θ * X * phaseGate θ * X * phaseGate φ₁) 2) ≤ 5 * δ := by
    have h := composition c_φ₁ c₃ (phaseGate φ₁) (phaseGate θ * X * phaseGate θ * X) (phaseGate_unitary φ₁) δ (4 * δ) hc_φ₁_err hc₃_err
    linarith
  set c₅ := c_H ++ c₄
  have hc₅_err : frobNorm (initializedMap c₅.unitary - idealMap (phaseGate θ * X * phaseGate θ * X * phaseGate φ₁ * oneQubit hadamard) 2) ≤ 5 * δ := by
    have h := composition c_H c₄ (oneQubit hadamard) (phaseGate θ * X * phaseGate θ * X * phaseGate φ₁) hadamard_unitary_aux 0 (5 * δ) hc_H_err hc₄_err
    linarith
  set c₆ := c_φ₂ ++ c₅
  have hc₆_err : frobNorm (initializedMap c₆.unitary - idealMap (phaseGate θ * X * phaseGate θ * X * phaseGate φ₁ * oneQubit hadamard * phaseGate φ₂) 2) ≤ 6 * δ := by
    have h := composition c_φ₂ c₅ (phaseGate φ₂) (phaseGate θ * X * phaseGate θ * X * phaseGate φ₁ * oneQubit hadamard) (phaseGate_unitary φ₂) δ (5 * δ) hc_φ₂_err hc₅_err
    linarith
  set c₇ := c_H ++ c₆
  have hc₇_err : frobNorm (initializedMap c₇.unitary - idealMap (phaseGate θ * X * phaseGate θ * X * phaseGate φ₁ * oneQubit hadamard * phaseGate φ₂ * oneQubit hadamard) 2) ≤ 6 * δ := by
    have h := composition c_H c₆ (oneQubit hadamard) (phaseGate θ * X * phaseGate θ * X * phaseGate φ₁ * oneQubit hadamard * phaseGate φ₂) hadamard_unitary_aux 0 (6 * δ) hc_H_err hc₆_err
    linarith
  set c₈ := c_φ₃ ++ c₇
  have hc₈_err : frobNorm (initializedMap c₈.unitary - idealMap (phaseGate θ * X * phaseGate θ * X * phaseGate φ₁ * oneQubit hadamard * phaseGate φ₂ * oneQubit hadamard * phaseGate φ₃) 2) ≤ 7 * δ := by
    have h := composition c_φ₃ c₇ (phaseGate φ₃) (phaseGate θ * X * phaseGate θ * X * phaseGate φ₁ * oneQubit hadamard * phaseGate φ₂ * oneQubit hadamard) (phaseGate_unitary φ₃) δ (6 * δ) hc_φ₃_err hc₇_err
    linarith
  use c₈
  have hU_eq : phaseGate θ * X * phaseGate θ * X * phaseGate φ₁ * oneQubit hadamard * phaseGate φ₂ * oneQubit hadamard * phaseGate φ₃ = U := by
    dsimp [X]
    exact hU_dec.symm
  rw [hU_eq] at hc₈_err
  refine ⟨?_, ?_⟩
  · have hbound := k_bound n ε hε (pow_ceil_bound ε hε)
    linarith
  · have hc_sz_sum : (c₈.size : ℝ) ≤ 7 * (A₀ * ((k : ℝ) + 1)) + 6 := by
      dsimp [c_H, c_pi_H, cX, c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, Circuit.size] at *
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_zero, Nat.cast_one]
      linarith
    have hsz_bound := size_bound A₀ hA₀_pos ε hε hε1
    linarith
