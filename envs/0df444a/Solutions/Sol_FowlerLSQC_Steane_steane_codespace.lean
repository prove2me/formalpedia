-- Prove2me | solution 1 for FowlerLSQC.Steane.steane_codespace
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T09:50:15.524209+00:00
-- url     : https://prove2.me/submissions/b2852b1c-1159-4667-bede-c0109f1dc081

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Definitions.Def_FowlerLSQC_Steane_stabilizer
import Definitions.Def_FowlerLSQC_Steane_logicalZ
import Definitions.Def_FowlerLSQC_Steane_logicalZero
import Definitions.Def_FowlerLSQC_Steane_logicalOne
import Definitions.Def_FowlerLSQC_Steane_plusOneEigenspace
import Mathlib.Tactic.LinearCombination

/-!
The exact Steane-code joint fixed subspaces, proved from the published definitions.
Finite word certificates, general Pauli action formulas, and the arbitrary-vector
decomposition are included below so the submission has no local helper imports.
-/

set_option autoImplicit false

namespace AuditSteane

abbrev Word := Fin 7 → Bool
abbrev Coeff := Fin 3 → Bool

def flipMasks : Fin 3 → Word :=
  ![![false, false, false, true, true, true, true],
    ![false, true, true, false, false, true, true],
    ![true, false, true, false, true, false, true]]

def xor (u v : Word) : Word := fun i => u i != v i

def parity (u v : Word) : Bool :=
  Bool.xor (Bool.xor (Bool.xor (u 0 && v 0) (u 1 && v 1)) (u 2 && v 2))
    (Bool.xor (Bool.xor (u 3 && v 3) (u 4 && v 4))
      (Bool.xor (u 5 && v 5) (u 6 && v 6)))

def passesZ (w : Word) : Prop :=
  parity w (flipMasks 0) = false ∧
  parity w (flipMasks 1) = false ∧
  parity w (flipMasks 2) = false

instance (w : Word) : Decidable (passesZ w) := by
  unfold passesZ
  infer_instance

def logicalZeroWords : Finset Word :=
  {![false, false, false, false, false, false, false],
   ![true, false, true, false, true, false, true],
   ![false, true, true, false, false, true, true],
   ![true, true, false, false, true, true, false],
   ![false, false, false, true, true, true, true],
   ![true, false, true, true, false, true, false],
   ![false, true, true, true, true, false, false],
   ![true, true, false, true, false, false, true]}

def logicalOneWords : Finset Word :=
  {![true, true, true, true, true, true, true],
   ![false, true, false, true, false, true, false],
   ![true, false, false, true, true, false, false],
   ![false, false, true, true, false, false, true],
   ![true, true, true, false, false, false, false],
   ![false, true, false, false, true, false, true],
   ![true, false, false, false, false, true, true],
   ![false, false, true, false, true, true, false]}

def encode (b : Bool) (c : Coeff) : Word := fun i =>
  Bool.xor (Bool.xor b (c 0 && flipMasks 0 i))
    (Bool.xor (c 1 && flipMasks 1 i) (c 2 && flipMasks 2 i))

def logicalZSign (w : Word) : Bool := Bool.xor (Bool.xor (w 0) (w 1)) (w 2)

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem zero_card : logicalZeroWords.card = 8 := by decide
theorem one_card : logicalOneWords.card = 8 := by decide
theorem supports_disjoint : Disjoint logicalZeroWords logicalOneWords := by decide

theorem kernel_exact_bits : ∀ a b c d e f g : Bool,
    passesZ ![a,b,c,d,e,f,g] ↔
      ![a,b,c,d,e,f,g] ∈ logicalZeroWords ∨ ![a,b,c,d,e,f,g] ∈ logicalOneWords := by decide

theorem kernel_exact (w : Word) :
    passesZ w ↔ w ∈ logicalZeroWords ∨ w ∈ logicalOneWords := by
  have hw : w = ![w 0, w 1, w 2, w 3, w 4, w 5, w 6] := by
    ext i
    fin_cases i <;> rfl
  conv_lhs => rw [hw]
  conv_rhs => rw [hw]
  exact kernel_exact_bits _ _ _ _ _ _ _

theorem zero_orbit : (Finset.univ.image (encode false)) = logicalZeroWords := by decide
theorem one_orbit : (Finset.univ.image (encode true)) = logicalOneWords := by decide

theorem encoding_injective : ∀ b b' : Bool, ∀ c c' : Coeff,
    encode b c = encode b' c' → b = b' ∧ c = c' := by decide

theorem logical_z_separates : ∀ b : Bool, ∀ c : Coeff,
    logicalZSign (encode b c) = b := by decide

theorem x_preserves_orbits : ∀ b : Bool, ∀ c : Coeff, ∀ k : Fin 3,
    xor (encode b c) (flipMasks k) = encode b (Function.update c k (!c k)) := by decide

theorem kernel_card : (Finset.univ.filter passesZ).card = 16 := by
  have heq : Finset.univ.filter passesZ = logicalZeroWords ∪ logicalOneWords := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact kernel_exact w
  rw [heq, Finset.card_union_of_disjoint supports_disjoint, zero_card, one_card]


/-- Apply one generator only when the corresponding coefficient is true. -/
def conditionalFlip (k : Fin 3) (a : Bool) (w : Word) : Word :=
  if a then xor w (flipMasks k) else w

theorem encode_as_flips_bits : ∀ b a₀ a₁ a₂ : Bool,
    encode b ![a₀, a₁, a₂] =
      conditionalFlip 2 a₂ (conditionalFlip 1 a₁
        (conditionalFlip 0 a₀ (fun _ => b))) := by decide

/-- Every encoded word is reached from its constant representative by three generators. -/
theorem encode_as_flips (b : Bool) (c : Coeff) :
    encode b c = conditionalFlip 2 (c 2) (conditionalFlip 1 (c 1)
      (conditionalFlip 0 (c 0) (fun _ => b))) := by
  have hc : c = ![c 0, c 1, c 2] := by
    ext i
    fin_cases i <;> rfl
  conv_lhs => rw [hc]
  exact encode_as_flips_bits b (c 0) (c 1) (c 2)

theorem invariant_conditionalFlip {α : Type*} (f : Word → α)
    (h : ∀ (k : Fin 3) (w : Word), f (xor w (flipMasks k)) = f w)
    (k : Fin 3) (a : Bool) (w : Word) :
    f (conditionalFlip k a w) = f w := by
  cases a
  · rfl
  · exact h k w

/-- Invariance under the three X masks makes any function constant on each encoded orbit. -/
theorem invariant_encode {α : Type*} (f : Word → α)
    (h : ∀ (k : Fin 3) (w : Word), f (xor w (flipMasks k)) = f w)
    (b : Bool) (c : Coeff) : f (encode b c) = f (fun _ => b) := by
  rw [encode_as_flips, invariant_conditionalFlip f h,
    invariant_conditionalFlip f h, invariant_conditionalFlip f h]

theorem invariant_zero {α : Type*} (f : Word → α)
    (h : ∀ (k : Fin 3) (w : Word), f (xor w (flipMasks k)) = f w)
    (w : Word) (hw : w ∈ logicalZeroWords) : f w = f (fun _ => false) := by
  rw [← zero_orbit, Finset.mem_image] at hw
  obtain ⟨c, _, rfl⟩ := hw
  exact invariant_encode f h false c

theorem invariant_one {α : Type*} (f : Word → α)
    (h : ∀ (k : Fin 3) (w : Word), f (xor w (flipMasks k)) = f w)
    (w : Word) (hw : w ∈ logicalOneWords) : f w = f (fun _ => true) := by
  rw [← one_orbit, Finset.mem_image] at hw
  obtain ⟨c, _, rfl⟩ := hw
  exact invariant_encode f h true c

theorem logical_z_zero (w : Word) (hw : w ∈ logicalZeroWords) :
    logicalZSign w = false := by
  rw [← zero_orbit, Finset.mem_image] at hw
  obtain ⟨c, _, rfl⟩ := hw
  exact logical_z_separates false c

theorem logical_z_one (w : Word) (hw : w ∈ logicalOneWords) :
    logicalZSign w = true := by
  rw [← one_orbit, Finset.mem_image] at hw
  obtain ⟨c, _, rfl⟩ := hw
  exact logical_z_separates true c


/-- Each X generator is an involution on bit strings. -/
theorem xor_cancel (w m : Word) : xor (xor w m) m = w := by
  ext i
  change ((w i != m i) != m i) = w i
  cases w i <;> cases m i <;> rfl

theorem x_preserves_zero (k : Fin 3) (w : Word) (hw : w ∈ logicalZeroWords) :
    xor w (flipMasks k) ∈ logicalZeroWords := by
  rw [← zero_orbit, Finset.mem_image] at hw ⊢
  obtain ⟨c, _, rfl⟩ := hw
  exact ⟨Function.update c k (!c k), Finset.mem_univ _, x_preserves_orbits false c k |>.symm⟩

theorem x_preserves_one (k : Fin 3) (w : Word) (hw : w ∈ logicalOneWords) :
    xor w (flipMasks k) ∈ logicalOneWords := by
  rw [← one_orbit, Finset.mem_image] at hw ⊢
  obtain ⟨c, _, rfl⟩ := hw
  exact ⟨Function.update c k (!c k), Finset.mem_univ _, x_preserves_orbits true c k |>.symm⟩

theorem xor_mem_zero_iff (k : Fin 3) (w : Word) :
    xor w (flipMasks k) ∈ logicalZeroWords ↔ w ∈ logicalZeroWords := by
  constructor
  · intro h
    have h' := x_preserves_zero k _ h
    simpa only [xor_cancel] using h'
  · exact x_preserves_zero k w

theorem xor_mem_one_iff (k : Fin 3) (w : Word) :
    xor w (flipMasks k) ∈ logicalOneWords ↔ w ∈ logicalOneWords := by
  constructor
  · intro h
    have h' := x_preserves_one k _ h
    simpa only [xor_cancel] using h'
  · exact x_preserves_one k w

theorem zero_word_mem : (fun _ => false) ∈ logicalZeroWords := by decide
theorem one_word_mem : (fun _ => true) ∈ logicalOneWords := by decide


end AuditSteane

set_option autoImplicit false

namespace S04Steane

open QAlgorithms QAlgorithms.Stabilizer
open scoped BigOperators

/-- A tensor product of bit flips, with no phase. -/
def xString {n : ℕ} (mask : Qubits n) : PauliString n :=
  ⟨0, fun i => if mask i then .X else .I⟩

/-- A tensor product of phase flips, with no phase. -/
def zString {n : ℕ} (mask : Qubits n) : PauliString n :=
  ⟨0, fun i => if mask i then .Z else .I⟩

theorem x_entry (m a b : Bool) :
    (if m then Pauli.X else Pauli.I).mat a b =
      if b = Bool.xor a m then (1 : ℂ) else 0 := by
  cases m <;> cases a <;> cases b <;> simp [Pauli.mat, pauliX]

theorem z_entry (m a b : Bool) :
    (if m then Pauli.Z else Pauli.I).mat a b =
      if b = a then (if m && a then (-1 : ℂ) else 1) else 0 := by
  cases m <;> cases a <;> cases b <;> simp [Pauli.mat, pauliZ]

/-- Every row of an X string has exactly one nonzero entry. -/
theorem xString_matrix {n : ℕ} (mask y z : Qubits n) :
    (xString mask).toMatrix y z =
      if z = (fun i => Bool.xor (y i) (mask i)) then (1 : ℂ) else 0 := by
  classical
  simp only [xString, PauliString.toMatrix, Matrix.of_apply,
    ZMod.val_zero, pow_zero, one_mul, x_entry]
  rw [Fintype.prod_boole]
  by_cases h : z = (fun i => Bool.xor (y i) (mask i))
  · have hall : ∀ i, z i = Bool.xor (y i) (mask i) := congrFun h
    rw [if_pos hall, if_pos h]
  · have hn : ¬ ∀ i, z i = Bool.xor (y i) (mask i) := fun hh => h (funext hh)
    rw [if_neg hn, if_neg h]

/-- Every Z string is diagonal. -/
theorem zString_matrix {n : ℕ} (mask y z : Qubits n) :
    (zString mask).toMatrix y z =
      if z = y then (∏ i, if mask i && y i then (-1 : ℂ) else 1) else 0 := by
  classical
  simp only [zString, PauliString.toMatrix, Matrix.of_apply,
    ZMod.val_zero, pow_zero, one_mul, z_entry]
  rw [Fintype.prod_ite_zero]
  by_cases h : z = y
  · have hall : ∀ i, z i = y i := congrFun h
    rw [if_pos hall, if_pos h]
  · have hn : ¬ ∀ i, z i = y i := fun hh => h (funext hh)
    rw [if_neg hn, if_neg h]

/-- The action of an X string is a coordinate permutation. -/
theorem act_xString {n : ℕ} (mask : Qubits n)
    (ψ : EuclideanSpace ℂ (Qubits n)) (y : Qubits n) :
    act (xString mask).toMatrix ψ y =
      ψ (fun i => Bool.xor (y i) (mask i)) := by
  classical
  change (∑ z, (xString mask).toMatrix y z * ψ z) = _
  simp [xString_matrix]

/-- The action of a Z string multiplies each coordinate by its parity sign. -/
theorem act_zString {n : ℕ} (mask : Qubits n)
    (ψ : EuclideanSpace ℂ (Qubits n)) (y : Qubits n) :
    act (zString mask).toMatrix ψ y =
      (∏ i, if mask i && y i then (-1 : ℂ) else 1) * ψ y := by
  classical
  change (∑ z, (zString mask).toMatrix y z * ψ z) = _
  simp [zString_matrix]

def mask7 : Fin 3 → Qubits 7 :=
  ![![false, false, false, true, true, true, true],
    ![false, true, true, false, false, true, true],
    ![true, false, true, false, true, false, true]]

theorem stabilizer_xString (k : Fin 3) :
    FowlerLSQC.Steane.stabilizer ⟨k.val, by omega⟩ = xString (mask7 k) := by
  fin_cases k
  all_goals
    change PauliString.mk 0 _ = PauliString.mk 0 _
    congr 1
    funext q
    fin_cases q <;> rfl

theorem stabilizer_zString (k : Fin 3) :
    FowlerLSQC.Steane.stabilizer ⟨k.val + 3, by omega⟩ = zString (mask7 k) := by
  fin_cases k
  all_goals
    change PauliString.mk 0 _ = PauliString.mk 0 _
    congr 1
    funext q
    fin_cases q <;> rfl

theorem act_stabilizer_x (k : Fin 3) (ψ : EuclideanSpace ℂ (Qubits 7))
    (y : Qubits 7) :
    act (FowlerLSQC.Steane.stabilizer ⟨k.val, by omega⟩).toMatrix ψ y =
      ψ (fun i => Bool.xor (y i) (mask7 k i)) := by
  rw [stabilizer_xString]
  exact act_xString _ _ _

theorem act_stabilizer_z (k : Fin 3) (ψ : EuclideanSpace ℂ (Qubits 7))
    (y : Qubits 7) :
    act (FowlerLSQC.Steane.stabilizer ⟨k.val + 3, by omega⟩).toMatrix ψ y =
      (∏ i, if mask7 k i && y i then (-1 : ℂ) else 1) * ψ y := by
  rw [stabilizer_zString]
  exact act_zString _ _ _

theorem logicalZ_zString :
    FowlerLSQC.Steane.logicalZ =
      zString ![true, true, true, false, false, false, false] := by
  change PauliString.mk 0 _ = PauliString.mk 0 _
  congr 1
  funext q
  fin_cases q <;> rfl

theorem act_logicalZ (ψ : EuclideanSpace ℂ (Qubits 7)) (y : Qubits 7) :
    act FowlerLSQC.Steane.logicalZ.toMatrix ψ y =
      (∏ i, if (![true, true, true, false, false, false, false] : Qubits 7) i && y i
        then (-1 : ℂ) else 1) * ψ y := by
  rw [logicalZ_zString]
  exact act_zString _ _ _

theorem sign_xor (a b : Bool) :
    (if Bool.xor a b then (-1 : ℂ) else 1) =
      (if a then (-1 : ℂ) else 1) * (if b then (-1 : ℂ) else 1) := by
  cases a <;> cases b <;> norm_num

theorem product_sign_parity (mask y : Qubits 7) :
    (∏ i, if mask i && y i then (-1 : ℂ) else 1) =
      if AuditSteane.parity y mask then (-1 : ℂ) else 1 := by
  unfold AuditSteane.parity
  rw [sign_xor, sign_xor, sign_xor, sign_xor, sign_xor, sign_xor]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  simp only [Bool.and_comm, mul_assoc]
  rfl

theorem act_stabilizer_x_xor (k : Fin 3) (ψ : EuclideanSpace ℂ (Qubits 7))
    (y : Qubits 7) :
    act (FowlerLSQC.Steane.stabilizer ⟨k.val, by omega⟩).toMatrix ψ y =
      ψ (AuditSteane.xor y (AuditSteane.flipMasks k)) := by
  exact act_stabilizer_x k ψ y

theorem act_stabilizer_z_parity (k : Fin 3) (ψ : EuclideanSpace ℂ (Qubits 7))
    (y : Qubits 7) :
    act (FowlerLSQC.Steane.stabilizer ⟨k.val + 3, by omega⟩).toMatrix ψ y =
      (if AuditSteane.parity y (AuditSteane.flipMasks k) then (-1 : ℂ) else 1) * ψ y := by
  rw [act_stabilizer_z, product_sign_parity]
  rfl

theorem act_logicalZ_parity (ψ : EuclideanSpace ℂ (Qubits 7)) (y : Qubits 7) :
    act FowlerLSQC.Steane.logicalZ.toMatrix ψ y =
      (if AuditSteane.logicalZSign y then (-1 : ℂ) else 1) * ψ y := by
  rw [act_logicalZ]
  congr 1
  unfold AuditSteane.logicalZSign
  rw [sign_xor, sign_xor]
  simp [Fin.prod_univ_succ]


end S04Steane

set_option autoImplicit false

namespace S04Steane

open QAlgorithms FowlerLSQC.Steane AuditSteane
open scoped BigOperators

noncomputable def normalization : ℂ := ((Real.sqrt 8 : ℝ) : ℂ)

theorem normalization_ne_zero : normalization ≠ 0 := by
  unfold normalization
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 8)))

theorem sum_ket_apply {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι) :
    (∑ w ∈ s, ket w) y = if y ∈ s then (1 : ℂ) else 0 := by
  classical
  simp [ket]

theorem bitString_vec (a b c d e f g : Fin 2) :
    FowlerLSQC.Steane.bitString ![a,b,c,d,e,f,g] =
      ![decide (a = 1), decide (b = 1), decide (c = 1), decide (d = 1),
        decide (e = 1), decide (f = 1), decide (g = 1)] := by
  funext i
  fin_cases i <;> rfl

theorem logicalZero_sum : logicalZero =
    normalization⁻¹ • ∑ w ∈ logicalZeroWords, ket w := by
  classical
  unfold logicalZero normalization logicalZeroWords
  congr 1
  simp [Finset.sum_insert, Finset.sum_singleton, bitString_vec, add_assoc]

theorem logicalOne_sum : logicalOne =
    normalization⁻¹ • ∑ w ∈ logicalOneWords, ket w := by
  classical
  unfold logicalOne normalization logicalOneWords
  congr 1
  simp [Finset.sum_insert, Finset.sum_singleton, bitString_vec, add_assoc]

theorem logicalZero_apply (y : Word) :
    logicalZero y = if y ∈ logicalZeroWords then normalization⁻¹ else 0 := by
  classical
  rw [logicalZero_sum]
  simp [sum_ket_apply]

theorem logicalOne_apply (y : Word) :
    logicalOne y = if y ∈ logicalOneWords then normalization⁻¹ else 0 := by
  classical
  rw [logicalOne_sum]
  simp [sum_ket_apply]

/-- Any function fixed by the three X masks and supported on the Z kernel
is determined by its two amplitudes at the orbit representatives. -/
theorem fixed_expansion (ψ : EuclideanSpace ℂ (Qubits 7))
    (hx : ∀ (k : Fin 3) (w : Word), ψ (xor w (flipMasks k)) = ψ w)
    (hz : ∀ w : Word, ¬ passesZ w → ψ w = 0) :
    ψ = (normalization * ψ (fun _ => false)) • logicalZero +
      (normalization * ψ (fun _ => true)) • logicalOne := by
  classical
  ext w
  by_cases h0 : w ∈ logicalZeroWords
  · have h1 : w ∉ logicalOneWords :=
      fun h1 => Finset.disjoint_left.mp supports_disjoint h0 h1
    have hw := invariant_zero (fun w => ψ w) hx w h0
    simp [logicalZero_apply, logicalOne_apply, h0, h1, hw,
      mul_assoc, mul_comm, mul_left_comm, normalization_ne_zero]
  · by_cases h1 : w ∈ logicalOneWords
    · have hw := invariant_one (fun w => ψ w) hx w h1
      simp [logicalZero_apply, logicalOne_apply, h0, h1, hw,
        mul_assoc, mul_comm, mul_left_comm, normalization_ne_zero]
    · have hw : ψ w = 0 := hz w (by simpa [kernel_exact, h0, h1])
      simp [logicalZero_apply, logicalOne_apply, h0, h1, hw]

theorem fixed_mem_span (ψ : EuclideanSpace ℂ (Qubits 7))
    (hx : ∀ (k : Fin 3) (w : Word), ψ (xor w (flipMasks k)) = ψ w)
    (hz : ∀ w : Word, ¬ passesZ w → ψ w = 0) :
    ψ ∈ Submodule.span ℂ {logicalZero, logicalOne} := by
  rw [fixed_expansion ψ hx hz]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem fixed_zero_mem_span (ψ : EuclideanSpace ℂ (Qubits 7))
    (hx : ∀ (k : Fin 3) (w : Word), ψ (xor w (flipMasks k)) = ψ w)
    (hz : ∀ w : Word, ¬ passesZ w → ψ w = 0)
    (hone : ψ (fun _ => true) = 0) :
    ψ ∈ Submodule.span ℂ {logicalZero} := by
  have heq := fixed_expansion ψ hx hz
  rw [hone, mul_zero, zero_smul, add_zero] at heq
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))


end S04Steane

set_option autoImplicit false

namespace S04Steane

open QAlgorithms QAlgorithms.Stabilizer FowlerLSQC.Steane AuditSteane

theorem passesZ_iff_forall (w : Word) :
    passesZ w ↔ ∀ k : Fin 3, parity w (flipMasks k) = false := by
  constructor
  · intro h k
    fin_cases k
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  · intro h
    exact ⟨h 0, h 1, h 2⟩

theorem complex_eq_zero_of_neg_eq (z : ℂ) (h : -z = z) : z = 0 := by
  linear_combination -(1 / 2 : ℂ) * h

theorem fixed_x_invariant (ψ : EuclideanSpace ℂ (Qubits 7))
    (h : ψ ∈ ⨅ k : Fin 6, plusOneEigenspace (stabilizer k))
    (k : Fin 3) (w : Word) : ψ (xor w (flipMasks k)) = ψ w := by
  have hk := ((Submodule.mem_iInf _).mp h) (⟨k.val, by omega⟩ : Fin 6)
  change act (stabilizer ⟨k.val, by omega⟩).toMatrix ψ = ψ at hk
  have hw := congrArg (fun v : EuclideanSpace ℂ (Qubits 7) => v w) hk
  simpa only [act_stabilizer_x_xor] using hw

theorem fixed_supported (ψ : EuclideanSpace ℂ (Qubits 7))
    (h : ψ ∈ ⨅ k : Fin 6, plusOneEigenspace (stabilizer k))
    (w : Word) (hw : ¬ passesZ w) : ψ w = 0 := by
  by_contra hn
  apply hw
  apply (passesZ_iff_forall w).mpr
  intro k
  have hk := ((Submodule.mem_iInf _).mp h) (⟨k.val + 3, by omega⟩ : Fin 6)
  change act (stabilizer ⟨k.val + 3, by omega⟩).toMatrix ψ = ψ at hk
  have he := congrArg (fun v : EuclideanSpace ℂ (Qubits 7) => v w) hk
  rw [act_stabilizer_z_parity] at he
  cases hp : parity w (flipMasks k)
  · rfl
  · simp only [hp, ↓reduceIte, neg_one_mul] at he
    exact False.elim (hn (complex_eq_zero_of_neg_eq _ he))

theorem mem_codespace_of_conditions (ψ : EuclideanSpace ℂ (Qubits 7))
    (hx : ∀ (k : Fin 3) (w : Word), ψ (xor w (flipMasks k)) = ψ w)
    (hz : ∀ (k : Fin 3) (w : Word),
      (if parity w (flipMasks k) then (-1 : ℂ) else 1) * ψ w = ψ w) :
    ψ ∈ ⨅ k : Fin 6, plusOneEigenspace (stabilizer k) := by
  apply (Submodule.mem_iInf _).mpr
  intro k
  change act (stabilizer k).toMatrix ψ = ψ
  rcases lt_or_ge k.val 3 with hk | hk
  · let j : Fin 3 := ⟨k.val, hk⟩
    have he : (⟨j.val, by omega⟩ : Fin 6) = k := rfl
    rw [← he]
    ext w
    rw [act_stabilizer_x_xor]
    exact hx j w
  · let j : Fin 3 := ⟨k.val - 3, by omega⟩
    have he : (⟨j.val + 3, by omega⟩ : Fin 6) = k := by
      apply Fin.ext
      dsimp [j]
      omega
    rw [← he]
    ext w
    rw [act_stabilizer_z_parity]
    exact hz j w

theorem logicalZero_fixed :
    logicalZero ∈ ⨅ k : Fin 6, plusOneEigenspace (stabilizer k) := by
  classical
  apply mem_codespace_of_conditions
  · intro k w
    simp only [logicalZero_apply, xor_mem_zero_iff]
  · intro k w
    by_cases hw : w ∈ logicalZeroWords
    · have hp := (passesZ_iff_forall w).mp ((kernel_exact w).mpr (Or.inl hw)) k
      simp [hp]
    · simp [logicalZero_apply, hw]

theorem logicalOne_fixed :
    logicalOne ∈ ⨅ k : Fin 6, plusOneEigenspace (stabilizer k) := by
  classical
  apply mem_codespace_of_conditions
  · intro k w
    simp only [logicalOne_apply, xor_mem_one_iff]
  · intro k w
    by_cases hw : w ∈ logicalOneWords
    · have hp := (passesZ_iff_forall w).mp ((kernel_exact w).mpr (Or.inr hw)) k
      simp [hp]
    · simp [logicalOne_apply, hw]

theorem logicalZero_logicalZ_fixed : logicalZero ∈ plusOneEigenspace logicalZ := by
  classical
  change act logicalZ.toMatrix logicalZero = logicalZero
  ext w
  rw [act_logicalZ_parity]
  by_cases hw : w ∈ logicalZeroWords
  · simp [logical_z_zero w hw]
  · simp [logicalZero_apply, hw]

theorem codespace_eq :
    (⨅ k : Fin 6, plusOneEigenspace (stabilizer k)) =
      Submodule.span ℂ {logicalZero, logicalOne} := by
  apply le_antisymm
  · intro ψ hψ
    exact fixed_mem_span ψ (fixed_x_invariant ψ hψ) (fixed_supported ψ hψ)
  · apply Submodule.span_le.mpr
    intro ψ hψ
    rcases Set.mem_insert_iff.mp hψ with rfl | hψ
    · exact logicalZero_fixed
    · have he : ψ = logicalOne := Set.mem_singleton_iff.mp hψ
      simpa [he] using logicalOne_fixed

theorem logicalZ_codespace_eq :
    (plusOneEigenspace logicalZ ⊓ ⨅ k : Fin 6, plusOneEigenspace (stabilizer k)) =
      Submodule.span ℂ {logicalZero} := by
  apply le_antisymm
  · intro ψ hψ
    have hz := hψ.1
    have hc := hψ.2
    change act logicalZ.toMatrix ψ = ψ at hz
    have he := congrArg (fun v : EuclideanSpace ℂ (Qubits 7) => v (fun _ => true)) hz
    rw [act_logicalZ_parity] at he
    have hone : ψ (fun _ => true) = 0 := by
      apply complex_eq_zero_of_neg_eq
      simpa [logicalZSign] using he
    exact fixed_zero_mem_span ψ (fixed_x_invariant ψ hc) (fixed_supported ψ hc) hone
  · apply Submodule.span_le.mpr
    intro ψ hψ
    have he : ψ = logicalZero := Set.mem_singleton_iff.mp hψ
    subst ψ
    exact ⟨logicalZero_logicalZ_fixed, logicalZero_fixed⟩

end S04Steane

open FowlerLSQC.Steane

theorem solution :
    (⨅ k : Fin 6, plusOneEigenspace (stabilizer k)) =
        Submodule.span ℂ {logicalZero, logicalOne} ∧
      (plusOneEigenspace logicalZ ⊓ ⨅ k : Fin 6, plusOneEigenspace (stabilizer k)) =
        Submodule.span ℂ {logicalZero} :=
  ⟨S04Steane.codespace_eq, S04Steane.logicalZ_codespace_eq⟩

#print axioms solution
