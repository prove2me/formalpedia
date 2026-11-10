-- Prove2me | solution 1 for EntanglingOps.BinaryPhase.binary_phase_protocol
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T16:09:35.439546+00:00
-- url     : https://prove2.me/submissions/add707b7-0043-449f-a22b-946569f1ab81

import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model
import Theorems.Thm_EntanglingOps_BinaryPhase_f_infinity_series_bounds

set_option autoImplicit false

namespace EntanglingOps.BinaryPhase.Probe91
open Matrix EntanglingOps.BinaryPhase
open scoped Kronecker

/-- explicit form of the gate: `cos β • 1 - (I sin β) • (σx ⊗ σx)` -/
noncomputable def G (β : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (Real.cos β : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) -
    (Complex.I * (Real.sin β : ℂ)) • (sx ⊗ₖ sx)

lemma sqrt2_sq : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 / 2 := by
  rw [← Complex.ofReal_mul]
  have h : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  rw [h]; push_cast; ring

lemma bellVec_apply (i : Fin 2 × Fin 2) (x y : Fin 2) :
    bellVec i (x, y) = ((1 / Real.sqrt 2 : ℝ) : ℂ) * pauli i y x := by
  simp only [bellVec, phiPlus, Fin.sum_univ_two]
  fin_cases x <;> simp [mul_comm]

lemma star_bell_mul (i j : Fin 2 × Fin 2) (a b c d : Fin 2) :
    star (bellVec i (a, b)) * star (bellVec j (c, d)) =
      (1 / 2 : ℂ) * (star (pauli i b a) * star (pauli j d c)) := by
  rw [bellVec_apply, bellVec_apply, star_mul', star_mul', Complex.star_def, Complex.conj_ofReal]
  rw [← sqrt2_sq]; ring

lemma sx_apply (a b : Fin 2) : sx a b = if a = b then 0 else 1 := by
  fin_cases a <;> fin_cases b <;> simp [sx, pauli]

lemma resource_apply (β : ℝ) (r1 a2 r2 b2 : Fin 2) :
    resource β ((r1, a2), (r2, b2)) = (1 / 2 : ℂ) *
      ((Real.cos β : ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) r1 a2 * (1 : Matrix (Fin 2) (Fin 2) ℂ) r2 b2)
        - Complex.I * (Real.sin β : ℂ) * (sx r1 a2 * sx r2 b2)) := by
  have h := sqrt2_sq
  simp only [resource, phiPlus, psiPlus, sx_apply, Matrix.one_apply]
  split_ifs <;> simp only [mul_zero, zero_mul, mul_one, sub_zero, zero_sub] <;>
    first
    | linear_combination (Real.cos β : ℂ) * h
    | linear_combination (-(Complex.I * (Real.sin β : ℂ))) * h
    | ring

lemma stepKraus_inner (β : ℝ) (i j : Fin 2 × Fin 2) :
    stepKraus β i j = (pauli i ⊗ₖ pauli j) * ((1 / 4 : ℂ) •
      ((Real.cos β : ℂ) • ((pauli i)ᴴ ⊗ₖ (pauli j)ᴴ) -
        (Complex.I * (Real.sin β : ℂ)) • ((sx * (pauli i)ᴴ) ⊗ₖ (sx * (pauli j)ᴴ)))) := by
  unfold stepKraus
  congr 1
  ext ⟨r1, r2⟩ ⟨c1, c2⟩
  simp only [of_apply, star_bell_mul, resource_apply, Matrix.smul_apply, Matrix.sub_apply, kroneckerMap_apply,
    mul_apply, conjTranspose_apply, smul_eq_mul, Fin.sum_univ_two, one_apply, sx_apply]
  fin_cases r1 <;> fin_cases r2 <;> simp <;> ring

lemma pauli_mul_conj (i : Fin 2 × Fin 2) : pauli i * (pauli i)ᴴ = 1 := by
  obtain ⟨a, b⟩ := i
  fin_cases a <;> fin_cases b <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    simp [pauli, mul_apply, Fin.sum_univ_two, conjTranspose_apply, one_apply]

lemma pauli_sx_conj (i : Fin 2 × Fin 2) :
    pauli i * sx * (pauli i)ᴴ = (if i.1 = 0 then (1 : ℂ) else -1) • sx := by
  obtain ⟨a, b⟩ := i
  fin_cases a <;> fin_cases b <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    simp [pauli, sx, mul_apply, Fin.sum_univ_two, conjTranspose_apply]

lemma stepKraus_eq (β : ℝ) (i j : Fin 2 × Fin 2) :
    stepKraus β i j = (1 / 4 : ℂ) • G (if succeeds (i, j) then β else -β) := by
  rw [stepKraus_inner, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul]
  simp only [← mul_kronecker_mul, ← Matrix.mul_assoc, pauli_mul_conj, pauli_sx_conj,
    one_kronecker_one, smul_kronecker, kronecker_smul, smul_smul]
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  fin_cases i1 <;> fin_cases j1 <;> simp [succeeds, G, Real.cos_neg, Real.sin_neg] <;> module

lemma sx_mul_sx : sx * sx = 1 := by
  ext x y; fin_cases x <;> fin_cases y <;> simp [sx, pauli, mul_apply, Fin.sum_univ_two]

lemma XX_sq : (sx ⊗ₖ sx) * (sx ⊗ₖ sx) = (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  rw [← mul_kronecker_mul, sx_mul_sx, one_kronecker_one]

lemma lin_mul (p q r s : ℂ) :
    (p • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - q • (sx ⊗ₖ sx)) *
      (r • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - s • (sx ⊗ₖ sx)) =
      (p * r + q * s) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - (p * s + q * r) • (sx ⊗ₖ sx) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, XX_sq, smul_smul]
  (module)

lemma G_mul (a b : ℝ) : G a * G b = G (a + b) := by
  unfold G
  rw [lin_mul]
  congr 2
  · push_cast [Real.cos_add]; linear_combination Complex.sin (a : ℂ) * Complex.sin (b : ℂ) * Complex.I_sq
  · push_cast [Real.sin_add]; ring

lemma G_zero : G 0 = 1 := by simp [G]

lemma G_neg_pi : G (-Real.pi) = -1 := by simp [G, Real.cos_neg, Real.sin_neg]

lemma G_conjTranspose (a : ℝ) : (G a)ᴴ = G (-a) := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
    simp [G, sx_apply, one_apply, conjTranspose_apply, Real.cos_neg, Real.sin_neg] <;>
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.conj_ofReal]

lemma G_unitary (a : ℝ) : (G a)ᴴ * G a = 1 := by
  rw [G_conjTranspose, G_mul, neg_add_cancel, G_zero]

/-! ### C1: closed form of the gate by diagonalisation -/

def Hm : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

lemma H_mul_H : Hm * Hm = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext x y; fin_cases x <;> fin_cases y <;> simp [Hm, mul_apply, Fin.sum_univ_two] <;> norm_num

lemma H_Z_H : Hm * pauli (1, 1) * Hm = (2 : ℂ) • sx := by
  ext x y; fin_cases x <;> fin_cases y <;> simp [Hm, sx, pauli, mul_apply, Fin.sum_univ_two] <;> norm_num

lemma U_mul_U : (Hm ⊗ₖ Hm) * (Hm ⊗ₖ Hm) = (4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  rw [← mul_kronecker_mul, H_mul_H, smul_kronecker, kronecker_smul, one_kronecker_one, smul_smul]
  norm_num

lemma U_right : (Hm ⊗ₖ Hm) * ((1 / 4 : ℂ) • (Hm ⊗ₖ Hm)) = 1 := by
  rw [Matrix.mul_smul, U_mul_U, smul_smul]; norm_num

lemma U_left : ((1 / 4 : ℂ) • (Hm ⊗ₖ Hm)) * (Hm ⊗ₖ Hm) = 1 := by
  rw [Matrix.smul_mul, U_mul_U, smul_smul]; norm_num

lemma U_unit : IsUnit (Hm ⊗ₖ Hm) := ⟨⟨Hm ⊗ₖ Hm, (1 / 4 : ℂ) • (Hm ⊗ₖ Hm), U_right, U_left⟩, rfl⟩

lemma U_inv : (Hm ⊗ₖ Hm)⁻¹ = (1 / 4 : ℂ) • (Hm ⊗ₖ Hm) := Matrix.inv_eq_right_inv U_right

lemma conj_D : (Hm ⊗ₖ Hm) * (pauli (1, 1) ⊗ₖ pauli (1, 1)) * (Hm ⊗ₖ Hm)⁻¹ = sx ⊗ₖ sx := by
  rw [U_inv, Matrix.mul_smul, ← mul_kronecker_mul, ← mul_kronecker_mul, H_Z_H, smul_kronecker,
    kronecker_smul, smul_smul, smul_smul]
  norm_num

lemma ZZ_diag : pauli (1, 1) ⊗ₖ pauli (1, 1) =
    diagonal (fun x : Fin 2 × Fin 2 => if x.1 = x.2 then (1 : ℂ) else -1) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [pauli, diagonal_apply]

lemma cexp_neg (a : ℝ) : NormedSpace.exp (-(Complex.I * (a : ℂ)) * 1) =
    (Real.cos a : ℂ) - Complex.I * (Real.sin a : ℂ) := by
  rw [← Complex.exp_eq_exp_ℂ, show -(Complex.I * (a : ℂ)) * 1 = ((-a : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_mul_I]
  push_cast; simp [Complex.cos_neg, Complex.sin_neg]; ring

lemma cexp_pos (a : ℝ) : NormedSpace.exp (-(Complex.I * (a : ℂ)) * -1) =
    (Real.cos a : ℂ) + Complex.I * (Real.sin a : ℂ) := by
  rw [← Complex.exp_eq_exp_ℂ, show -(Complex.I * (a : ℂ)) * -1 = ((a : ℝ) : ℂ) * Complex.I by
    ring, Complex.exp_mul_I]
  push_cast; ring

lemma exp_ZZ (a : ℝ) : NormedSpace.exp ((-(Complex.I * (a : ℂ))) • (pauli (1, 1) ⊗ₖ pauli (1, 1))) =
    (Real.cos a : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) -
      (Complex.I * (Real.sin a : ℂ)) • (pauli (1, 1) ⊗ₖ pauli (1, 1)) := by
  rw [ZZ_diag, ← diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  ext x y
  rcases eq_or_ne x y with rfl | h
  · simp only [diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, Pi.smul_apply,
      smul_eq_mul]
    split_ifs
    · rw [cexp_neg]; ring
    · rw [cexp_pos]; ring
  · simp [diagonal_apply_ne _ h, one_apply_ne h]

theorem gate_eq (a : ℝ) : gate a = G a := by
  have hX : (-(Complex.I * (a : ℂ))) • (sx ⊗ₖ sx) =
      (Hm ⊗ₖ Hm) * ((-(Complex.I * (a : ℂ))) • (pauli (1, 1) ⊗ₖ pauli (1, 1))) * (Hm ⊗ₖ Hm)⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul, conj_D]
  have hUU : (Hm ⊗ₖ Hm) * (Hm ⊗ₖ Hm)⁻¹ = 1 := by rw [U_inv]; exact U_right
  unfold gate
  rw [hX, Matrix.exp_conj _ _ U_unit, exp_ZZ, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hUU, Matrix.mul_smul, Matrix.smul_mul, conj_D]
  rfl

/-! ### C4: branch operators -/

lemma branch_append (N m : ℕ) (l l' : List Outcome) :
    branchKrausFrom N m (l ++ l') = branchKrausFrom N (m + l.length) l' * branchKrausFrom N m l := by
  induction l generalizing m with
  | nil => simp [branchKrausFrom]
  | cons o l ih =>
    rw [List.cons_append, branchKrausFrom, branchKrausFrom, ih, Matrix.mul_assoc, List.length_cons,
      show m + 1 + l.length = m + (l.length + 1) by omega]

lemma fail_branch (N : ℕ) (l : List Outcome) (hl : ∀ o ∈ l, ¬ succeeds o) (m : ℕ) :
    branchKrausFrom N m l =
      ((1 / 4 : ℂ) ^ l.length) • G (-((2 : ℝ) ^ m * (2 ^ l.length - 1) * alphaN N)) := by
  induction l generalizing m with
  | nil => simp [branchKrausFrom, G_zero]
  | cons o l ih =>
    have ho : ¬ succeeds o := hl o (List.mem_cons_self ..)
    rw [branchKrausFrom, ih (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')) (m + 1), stepKraus_eq]
    simp only [Prod.mk.eta]
    rw [if_neg ho, Matrix.smul_mul, Matrix.mul_smul, smul_smul, G_mul, List.length_cons,
      show (1 / 4 : ℂ) ^ l.length * (1 / 4) = (1 / 4) ^ (l.length + 1) by ring]
    congr 2
    ring

lemma failing_props {k : ℕ} {l : List Outcome} (h : l ∈ failing k) :
    l.length = k ∧ ∀ o ∈ l, ¬ succeeds o := by
  simp only [failing, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨f, hf, rfl⟩ := h
  refine ⟨List.length_ofFn .., fun o ho => ?_⟩
  simp only [List.mem_ofFn] at ho
  obtain ⟨s, rfl⟩ := ho
  exact hf s

lemma fail_K (N : ℕ) {k : ℕ} {l : List Outcome} (h : l ∈ failing k) :
    branchKraus N l = ((1 / 4 : ℂ) ^ k) • G (-((2 ^ k - 1) * alphaN N)) := by
  obtain ⟨hlen, hfail⟩ := failing_props h
  rw [branchKraus, fail_branch N l hfail 0, hlen, pow_zero, one_mul]

lemma term_K (N : ℕ) {l : List Outcome} (h : l ∈ terminal N) :
    ∃ k < N, l.length = k + 1 ∧
      (branchKraus N l = ((1 / 4 : ℂ) ^ (k + 1)) • G (alphaN N) ∨
        branchKraus N l = (-(1 / 4 : ℂ) ^ (k + 1)) • G (alphaN N)) := by
  simp only [terminal, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_product,
    Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨k, hk, ⟨f, o⟩, ⟨hf, ho⟩, rfl⟩ := h
  obtain ⟨hlen, hfail⟩ := failing_props hf
  refine ⟨k, hk, by simp [hlen], ?_⟩
  have hK : branchKraus N (f ++ [o]) =
      stepKraus (2 ^ k * alphaN N) o.1 o.2 * (((1 / 4 : ℂ) ^ k) • G (-((2 ^ k - 1) * alphaN N))) := by
    rw [branchKraus, branch_append, ← branchKraus, fail_K N hf, hlen]
    simp [branchKrausFrom]
  rw [hK, stepKraus_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, G_mul,
    show (1 / 4 : ℂ) * (1 / 4) ^ k = (1 / 4) ^ (k + 1) by ring]
  simp only [Prod.mk.eta]
  by_cases hs : succeeds o
  · left
    rw [if_pos hs]
    congr 2
    ring
  · right
    have hk1 : k + 1 = N := ho.resolve_left hs
    have hpi : (2 : ℝ) ^ (k + 1) * alphaN N = Real.pi := by
      rw [hk1, alphaN]; field_simp
    rw [if_neg hs, show -(2 ^ k * alphaN N) + -((2 ^ k - 1) * alphaN N) = -Real.pi + alphaN N by
      linear_combination -hpi, ← G_mul, G_neg_pi, neg_mul, Matrix.one_mul, smul_neg, neg_smul]

lemma card_fail_outcomes : (Finset.univ.filter fun o : Outcome => ¬ succeeds o).card = 8 := by
  decide

lemma card_failing (k : ℕ) : (failing k).card = 8 ^ k := by
  rw [failing, Finset.card_image_of_injective _ List.ofFn_injective]
  have : (Finset.univ.filter fun f : Fin k → Outcome => ∀ s, ¬ succeeds (f s)) =
      Fintype.piFinset (fun _ : Fin k => Finset.univ.filter fun o : Outcome => ¬ succeeds o) := by
    ext f; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset, Finset.prod_const, card_fail_outcomes, Finset.card_univ,
    Fintype.card_fin]

lemma star_quarter_pow (j : ℕ) : star ((1 / 4 : ℂ) ^ j) = (1 / 4 : ℂ) ^ j := by
  have h4 : star (1 / 4 : ℂ) = 1 / 4 := by
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, Complex.star_def, Complex.conj_ofReal]
  rw [star_pow, h4]

lemma trace_conj (θ : ℝ) (c : ℂ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix.trace ((c • G θ) * ρ * (c • G θ)ᴴ) = (c * star c) * Matrix.trace ρ := by
  rw [conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, G_unitary, Matrix.one_mul]
  ring

lemma reachProb_eq (N : ℕ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (k : ℕ) :
    reachProb N ρ k = (1 / 2 : ℝ) ^ (k - 1) * (Matrix.trace ρ).re := by
  unfold reachProb
  rw [Finset.sum_congr rfl (fun l hl => by rw [fail_K N hl, trace_conj])]
  rw [Finset.sum_const, card_failing, nsmul_eq_mul, star_quarter_pow, ← mul_pow,
    show ((1 / 4 : ℂ) * (1 / 4)) ^ (k - 1) = (((1 / 16 : ℝ) ^ (k - 1) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, ← mul_assoc]
  push_cast
  rw [← mul_pow]
  norm_num

/-! ### C4 rest: part 1, part 2, communication, entanglement -/

lemma part1 (N : ℕ) : ∀ l ∈ terminal N, ∃ c : ℂ, branchKraus N l = c • gate (alphaN N) := by
  intro l hl
  obtain ⟨k, -, -, h | h⟩ := term_K N hl
  · exact ⟨_, by rw [h, gate_eq]⟩
  · exact ⟨_, by rw [h, gate_eq]⟩

lemma geom_half (M : ℕ) : ∑ k ∈ Finset.range M, (1 / 2 : ℂ) ^ (k + 1) + (1 / 2 : ℂ) ^ M = 1 := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ]; linear_combination ih

lemma card_succ_outcomes : (Finset.univ.filter fun o : Outcome => succeeds o).card = 8 := by
  decide

lemma card_piece_filter (N k : ℕ) :
    (Finset.univ.filter fun o : Outcome => succeeds o ∨ k + 1 = N).card =
      if k + 1 = N then 16 else 8 := by
  split_ifs with h
  · have : (Finset.univ.filter fun o : Outcome => succeeds o ∨ k + 1 = N) = Finset.univ := by
      ext o; simp [h]
    rw [this, Finset.card_univ]
    simp [Fintype.card_prod]
  · have : (Finset.univ.filter fun o : Outcome => succeeds o ∨ k + 1 = N) =
        Finset.univ.filter fun o : Outcome => succeeds o := by
      ext o; simp [h]
    rw [this, card_succ_outcomes]

lemma piece_mem {N k : ℕ} {l : List Outcome}
    (h : l ∈ (failing k ×ˢ Finset.univ.filter fun o : Outcome => succeeds o ∨ k + 1 = N).image
      fun p : List Outcome × Outcome => p.1 ++ [p.2]) :
    l.length = k + 1 := by
  simp only [Finset.mem_image, Finset.mem_product] at h
  obtain ⟨⟨f, o⟩, ⟨hf, -⟩, rfl⟩ := h
  simp [(failing_props hf).1]

lemma append_single_inj : Function.Injective fun p : List Outcome × Outcome => p.1 ++ [p.2] := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  have h' : a ++ [x] = b ++ [y] := h
  obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
  simp only [List.cons.injEq, and_true] at h2
  rw [h1, h2]

lemma KK_term (N : ℕ) {l : List Outcome} (h : l ∈ terminal N) :
    (branchKraus N l)ᴴ * branchKraus N l =
      ((1 / 16 : ℂ) ^ l.length) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  obtain ⟨k, -, hlen, hK | hK⟩ := term_K N h <;>
    rw [hK, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, G_unitary, hlen]
  · rw [star_quarter_pow, ← mul_pow]; norm_num
  · rw [star_neg, star_quarter_pow, neg_mul_neg, ← mul_pow]; norm_num

lemma piece_sum (N k : ℕ) :
    ∑ l ∈ (failing k ×ˢ Finset.univ.filter fun o : Outcome => succeeds o ∨ k + 1 = N).image
        (fun p : List Outcome × Outcome => p.1 ++ [p.2]), (1 / 16 : ℂ) ^ l.length =
      ((8 ^ k * (if k + 1 = N then 16 else 8) : ℕ) : ℂ) * (1 / 16 : ℂ) ^ (k + 1) := by
  rw [Finset.sum_congr rfl (fun l hl => by rw [piece_mem hl]), Finset.sum_const, nsmul_eq_mul,
    Finset.card_image_of_injective _ append_single_inj, Finset.card_product, card_failing,
    card_piece_filter]

lemma eight_sixteen (k : ℕ) : (8 : ℂ) ^ k * (1 / 16) ^ k = (1 / 2) ^ k := by
  rw [← mul_pow]; norm_num

lemma part2 (N : ℕ) (hN : 1 ≤ N) :
    ∑ l ∈ terminal N, (branchKraus N l)ᴴ * branchKraus N l = 1 := by
  rw [Finset.sum_congr rfl (fun l hl => KK_term N hl), ← Finset.sum_smul]
  suffices hs : ∑ l ∈ terminal N, (1 / 16 : ℂ) ^ l.length = 1 by rw [hs, one_smul]
  have hdisj : ((Finset.range N : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun k =>
      (failing k ×ˢ Finset.univ.filter fun o : Outcome => succeeds o ∨ k + 1 = N).image
        fun p : List Outcome × Outcome => p.1 ++ [p.2]) := by
    intro a _ b _ hab
    show Disjoint _ _
    exact Finset.disjoint_left.2 fun l ha hb =>
      hab (by have h1 := piece_mem ha; have h2 := piece_mem hb; omega)
  unfold terminal
  rw [Finset.sum_biUnion hdisj, Finset.sum_congr rfl (fun k _ => piece_sum N k)]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hlast : ((8 ^ M * 16 : ℕ) : ℂ) * (1 / 16 : ℂ) ^ (M + 1) = (1 / 2) ^ M := by
    push_cast; linear_combination eight_sixteen M
  have hbody : ∀ k ∈ Finset.range M,
      ((8 ^ k * (if k + 1 = M + 1 then 16 else 8) : ℕ) : ℂ) * (1 / 16 : ℂ) ^ (k + 1) =
        (1 / 2 : ℂ) ^ (k + 1) := by
    intro k hk
    rw [if_neg (by simp only [Finset.mem_range] at hk; omega)]
    push_cast; linear_combination (1 / 2 : ℂ) * eight_sixteen k
  rw [Finset.sum_range_succ, if_pos (rfl : M + 1 = M + 1), hlast, Finset.sum_congr rfl hbody,
    geom_half]

lemma geom_Icc (M : ℕ) : ∑ k ∈ Finset.Icc 1 (M + 1), (1 / 2 : ℝ) ^ (k - 1) = 2 - (1 / 2) ^ M := by
  induction M with
  | zero => norm_num [Finset.Icc_self]
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, show M + 1 + 1 - 1 = M + 1 by omega]
    ring

lemma avgComm_eq (N : ℕ) (hN : 1 ≤ N) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : ρ.trace = 1) : avgComm N ρ = 2 - (1 / 2 : ℝ) ^ ((N : ℤ) - 2) := by
  have hre : (Matrix.trace ρ).re = 1 := by rw [hρ]; simp
  unfold avgComm
  simp only [reachProb_eq, hre, mul_one]
  rcases Nat.lt_or_ge N 2 with h | h
  · obtain rfl : N = 1 := by omega
    rw [show (1 : ℕ) - 1 = 0 from rfl, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    norm_num [_root_.zpow_neg, zpow_one]
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
    rw [show M + 2 - 1 = M + 1 by omega, geom_Icc,
      show ((M + 2 : ℕ) : ℤ) - 2 = (M : ℤ) by push_cast; ring, zpow_natCast]

lemma reidx (a b : ℕ) :
    (1 / 2 : ℝ) ^ a * entEntropy (resource (2 ^ a * alphaN (a + b))) =
      alphaN (a + b) * (1 / Real.pi) * 2 ^ b * entEntropy (resource (alphaN b)) := by
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  have h1 : (2 : ℝ) ^ a * alphaN (a + b) = alphaN b := by
    unfold alphaN; rw [pow_add]; field_simp
  have h2 : alphaN (a + b) * (1 / Real.pi) * 2 ^ b = (1 / 2) ^ a := by
    unfold alphaN; rw [pow_add]; field_simp
    rw [← mul_pow]; norm_num
  rw [h1, h2]

lemma avgEnt_eq (N : ℕ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : ρ.trace = 1) : avgEnt N ρ = alphaN N * fN N := by
  have hre : (Matrix.trace ρ).re = 1 := by rw [hρ]; simp
  unfold avgEnt fN
  simp only [reachProb_eq, hre, mul_one]
  rw [← mul_assoc, Finset.mul_sum]
  refine Finset.sum_nbij' (fun k => N + 1 - k) (fun k => N + 1 - k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have h := reidx (k - 1) (N + 1 - k)
    rw [show k - 1 + (N + 1 - k) = N by omega] at h
    rw [h]; ring

lemma part3 (N : ℕ) (hN : 1 ≤ N) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : ρ.trace = 1) :
    (∀ k ∈ Finset.Icc 1 N, reachProb N ρ k = (1 / 2 : ℝ) ^ (k - 1)) ∧
      avgEnt N ρ = alphaN N * fN N ∧
      avgComm N ρ = 2 - (1 / 2 : ℝ) ^ ((N : ℤ) - 2) := by
  have hre : (Matrix.trace ρ).re = 1 := by rw [hρ]; simp
  exact ⟨fun k _ => by rw [reachProb_eq, hre, mul_one], avgEnt_eq N ρ hρ, avgComm_eq N hN ρ hρ⟩

/-! ### C5: entanglement entropy of the resource state -/

noncomputable def Pm : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun x y => if x.1 = x.2 ∧ y.1 = y.2 then 1 / 2 else 0

noncomputable def Qm : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun x y => if x.1 ≠ x.2 ∧ y.1 ≠ y.2 then 1 / 2 else 0

lemma PP : Pm * Pm = Pm := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Pm, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

lemma QQ : Qm * Qm = Qm := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Qm, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

lemma PQ : Pm * Qm = 0 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Pm, Qm, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma QP : Qm * Pm = 0 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Pm, Qm, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma trP : Matrix.trace Pm = 1 := by
  simp [Matrix.trace, Pm, Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

lemma trQ : Matrix.trace Qm = 1 := by
  simp [Matrix.trace, Qm, Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

lemma star_half : star (1 / 2 : ℂ) = 1 / 2 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.star_def, Complex.conj_ofReal]

lemma Pm_herm : Pmᴴ = Pm := by
  ext x y
  simp only [conjTranspose_apply, Pm, of_apply]
  split_ifs <;> first | exact star_half | (exfalso; tauto) | simp

lemma Qm_herm : Qmᴴ = Qm := by
  ext x y
  simp only [conjTranspose_apply, Qm, of_apply]
  split_ifs <;> first | exact star_half | (exfalso; tauto) | simp

lemma Am_sa (a b : ℝ) : IsSelfAdjoint ((a : ℂ) • Pm + (b : ℂ) • Qm) := by
  unfold IsSelfAdjoint
  rw [star_eq_conjTranspose]
  simp only [conjTranspose_add, conjTranspose_smul, Pm_herm, Qm_herm, Complex.star_def,
    Complex.conj_ofReal]

lemma algMap_eq (r : ℝ) :
    algebraMap ℝ (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) r = (r : ℂ) • 1 := by
  rw [Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

lemma annih (a b : ℝ) :
    ((a : ℂ) • Pm + (b : ℂ) • Qm) * (((a : ℂ) • Pm + (b : ℂ) • Qm) - (a : ℂ) • 1) *
      (((a : ℂ) • Pm + (b : ℂ) • Qm) - (b : ℂ) • 1) = 0 := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [Pm, Qm, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, one_apply] <;> ring1

lemma spec_mem (a b x : ℝ) (hx : x ∈ spectrum ℝ ((a : ℂ) • Pm + (b : ℂ) • Qm)) :
    x = 0 ∨ x = a ∨ x = b := by
  have hp := spectrum.subset_polynomial_aeval ((a : ℂ) • Pm + (b : ℂ) • Qm)
    (Polynomial.X * (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b)) ⟨x, hx, rfl⟩
  simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, algMap_eq, annih,
    spectrum.zero_eq, Set.mem_singleton_iff, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at hp
  rcases mul_eq_zero.1 hp with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.1 h))
  · exact Or.inr (Or.inr (sub_eq_zero.1 h))

lemma interp (a b fa fb : ℝ) (ha : a = 0 → fa = 0) (hb : b = 0 → fb = 0) (hab : a = b → fa = fb) :
    ∃ α β : ℝ, fa = α * a + β * a ^ 2 ∧ fb = α * b + β * b ^ 2 := by
  by_cases h0a : a = 0
  · by_cases h0b : b = 0
    · exact ⟨0, 0, by simp [ha h0a], by simp [hb h0b]⟩
    · exact ⟨fb / b, 0, by simp [ha h0a, h0a], by rw [div_mul_cancel₀ _ h0b]; ring⟩
  · by_cases h0b : b = 0
    · exact ⟨fa / a, 0, by rw [div_mul_cancel₀ _ h0a]; ring, by simp [hb h0b, h0b]⟩
    · by_cases h : a = b
      · have e := hab h
        subst h
        exact ⟨fa / a, 0, by rw [div_mul_cancel₀ _ h0a]; ring,
          by rw [div_mul_cancel₀ _ h0a, e]; ring⟩
      · have hne : a * b * (b - a) ≠ 0 :=
          mul_ne_zero (mul_ne_zero h0a h0b) (sub_ne_zero.2 (Ne.symm h))
        refine ⟨(fa * b ^ 2 - fb * a ^ 2) / (a * b * (b - a)), (fb * a - fa * b) / (a * b * (b - a)),
          ?_, ?_⟩ <;>
        · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hne]; ring

lemma vn_two (a b : ℝ) :
    QAlgorithms.vnEntropy ((a : ℂ) • Pm + (b : ℂ) • Qm) =
      -(a * Real.logb 2 a + b * Real.logb 2 b) := by
  obtain ⟨α, β, h1, h2⟩ := interp a b (a * Real.logb 2 a) (b * Real.logb 2 b)
    (fun h => by simp [h]) (fun h => by simp [h]) (fun h => by rw [h])
  have hA := Am_sa a b
  set q : Polynomial ℝ := Polynomial.C α * Polynomial.X + Polynomial.C β * Polynomial.X ^ 2 with hq
  unfold QAlgorithms.vnEntropy
  rw [cfc_congr (g := fun x : ℝ => Polynomial.eval x q) ?_, cfc_polynomial q _ hA]
  · have ht : Matrix.trace (Polynomial.aeval ((a : ℂ) • Pm + (b : ℂ) • Qm) q) =
        ((α * (a + b) + β * (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
      simp only [hq, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, algMap_eq,
        Matrix.smul_mul, Matrix.one_mul, sq, Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
        PP, QQ, PQ, QP, smul_zero, add_zero, zero_add, smul_smul, Matrix.trace_add, Matrix.trace_smul,
        trP, trQ, smul_eq_mul, mul_one]
      push_cast; ring
    rw [ht, Complex.ofReal_re]
    linear_combination h1 + h2
  · intro x hx
    simp only [hq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow]
    rcases spec_mem a b x hx with rfl | rfl | rfl
    · simp
    · linarith [h1]
    · linarith [h2]

noncomputable def psiCS (c s : ℝ) : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) → ℂ := fun x =>
  (1 / 2 : ℂ) * ((c : ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) x.1.1 x.1.2 *
      (1 : Matrix (Fin 2) (Fin 2) ℂ) x.2.1 x.2.2) -
    Complex.I * (s : ℂ) * (sx x.1.1 x.1.2 * sx x.2.1 x.2.2))

lemma resource_psiCS (β : ℝ) : resource β = psiCS (Real.cos β) (Real.sin β) := by
  funext ⟨⟨r1, a2⟩, ⟨r2, b2⟩⟩
  rw [resource_apply]; rfl

lemma rhoA_eq (c s : ℝ) :
    WildeQIT.partialTraceRight (vecMulVec (psiCS c s) (star (psiCS c s))) =
      ((c ^ 2 : ℝ) : ℂ) • Pm + ((s ^ 2 : ℝ) : ℂ) • Qm := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  simp only [WildeQIT.partialTraceRight, of_apply, vecMulVec_apply, Pi.star_apply, psiCS,
    Fintype.sum_prod_type, Fin.sum_univ_two, one_apply, sx_apply, Pm, Qm, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [Complex.conj_ofReal] <;>
    first
    | ring1
    | linear_combination (-(1 / 2 : ℂ) * (s : ℂ) ^ 2) * Complex.I_sq
    | linear_combination ((1 / 2 : ℂ) * (s : ℂ) ^ 2) * Complex.I_sq

theorem entEntropy_resource (β : ℝ) :
    entEntropy (resource β) = -(Real.cos β ^ 2 * Real.logb 2 (Real.cos β ^ 2) +
      Real.sin β ^ 2 * Real.logb 2 (Real.sin β ^ 2)) := by
  rw [entEntropy, resource_psiCS, rhoA_eq, vn_two]

end EntanglingOps.BinaryPhase.Probe91

open EntanglingOps.BinaryPhase Matrix in
open scoped ComplexOrder in
theorem solution (N : ℕ) (hN : 1 ≤ N) :
    (∀ l ∈ terminal N, ∃ c : ℂ, branchKraus N l = c • gate (alphaN N)) ∧
    ∑ l ∈ terminal N, (branchKraus N l)ᴴ * branchKraus N l = 1 ∧
    (∀ ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, ρ.PosSemidef → ρ.trace = 1 →
      (∀ k ∈ Finset.Icc 1 N, reachProb N ρ k = (1 / 2 : ℝ) ^ (k - 1)) ∧
      avgEnt N ρ = alphaN N * fN N ∧
      avgComm N ρ = 2 - (1 / 2 : ℝ) ^ ((N : ℤ) - 2)) ∧
    fN N < fInf ∧
    Summable (fun k : ℕ => (2 : ℝ) ^ (k + 1) * entEntropy (resource (alphaN (k + 1)))) ∧
    (5.97931 : ℝ) < fInf ∧ fInf < 5.97932 := by
  obtain ⟨hs, hlt, hlo, hhi⟩ := EntanglingOps.BinaryPhase.f_infinity_series_bounds
    (fun k => (2 : ℝ) ^ k * entEntropy (resource (alphaN k)))
    (fun k => by simp only [EntanglingOps.BinaryPhase.Probe91.entEntropy_resource, alphaN])
  refine ⟨EntanglingOps.BinaryPhase.Probe91.part1 N, EntanglingOps.BinaryPhase.Probe91.part2 N hN,
    fun ρ _ hρ => EntanglingOps.BinaryPhase.Probe91.part3 N hN ρ hρ, ?_, hs, hlo, hhi⟩
  rw [fN, fInf]
  exact mul_lt_mul_of_pos_left (hlt N) (by positivity)
