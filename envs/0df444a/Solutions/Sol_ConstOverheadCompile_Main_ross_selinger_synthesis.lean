-- Prove2me | solution 1 for ConstOverheadCompile.Main.ross_selinger_synthesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-14T03:21:00.153736+00:00
-- url     : https://prove2.me/submissions/14b521d5-6568-425a-9267-947c3b9532b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets
import Definitions.Def_SpectralGapConjecture_HeckeSU
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Theorems.Thm_QEC_Distillation_axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
import Theorems.Thm_QEC_Distillation_closedSubgroup_eq_top_of_contains_nonparallel_axisCircles
import Theorems.Thm_QEC_Distillation_isClosed_specialUnitaryGeneratedClosure
import Theorems.Thm_QEC_Distillation_mem_specialUnitaryGeneratedClosure_iff
import Theorems.Thm_SpectralGapConjecture_bourgain_gamburd_SUd
import Theorems.Thm_ConstOverheadCompile_Main_decomposition_cnot_h_rotation

set_option autoImplicit false

/-!
# Bourgain-Gamburd `{H, T}` Generator Set, Algebraicity, `SU(2)` Density, and Word-to-Circuit Bridge
-/


/-! ### 1. Equivalence `Fin 2 ≃ Qubits 1` and Generators -/

def pb_bg_fin2EquivQubits1 : Fin 2 ≃ QAlgorithms.Qubits 1 where
  toFun i := fun _ => decide (i = 1)
  invFun q := if q 0 then 1 else 0
  left_inv i := by fin_cases i <;> rfl
  right_inv q := by
    ext a
    have ha : a = 0 := Subsingleton.elim a 0
    subst ha
    cases h : q 0 <;> simp [h]

noncomputable def pb_bg_H_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.sqrt 2 : ℂ)⁻¹), ((Real.sqrt 2 : ℂ)⁻¹);
     ((Real.sqrt 2 : ℂ)⁻¹), -((Real.sqrt 2 : ℂ)⁻¹)]

noncomputable def pb_bg_gen0_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I • pb_bg_H_mat

noncomputable def pb_bg_gen1_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-Complex.I * Real.pi / 8), 0;
     0, Complex.exp (Complex.I * Real.pi / 8)]

private theorem pb_bg_sqrt2_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private theorem pb_bg_sqrt2_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'

private theorem pb_bg_exp_pi8_conj :
    star (Complex.exp (-Complex.I * Real.pi / 8)) = Complex.exp (Complex.I * Real.pi / 8) := by
  rw [show -Complex.I * Real.pi / 8 = ((-(Real.pi / 8) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

private theorem pb_bg_exp_pi8_conj' :
    star (Complex.exp (Complex.I * Real.pi / 8)) = Complex.exp (-Complex.I * Real.pi / 8) := by
  rw [show Complex.I * Real.pi / 8 = ((Real.pi / 8 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

private theorem pb_bg_exp_pi8_mul_neg :
    Complex.exp (-Complex.I * Real.pi / 8) * Complex.exp (Complex.I * Real.pi / 8) = 1 := by
  rw [← Complex.exp_add, show -Complex.I * Real.pi / 8 + Complex.I * Real.pi / 8 = 0 by ring,
    Complex.exp_zero]

private theorem pb_bg_exp_pi8_neg_mul :
    Complex.exp (Complex.I * Real.pi / 8) * Complex.exp (-Complex.I * Real.pi / 8) = 1 := by
  rw [← Complex.exp_add, show Complex.I * Real.pi / 8 + -Complex.I * Real.pi / 8 = 0 by ring,
    Complex.exp_zero]

private theorem pb_bg_gen0_mem_SU2 :
    pb_bg_gen0_mat ∈ SpectralGapConjecture.SU 2 := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  have hunit : star pb_bg_gen0_mat * pb_bg_gen0_mat = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pb_bg_gen0_mat, pb_bg_H_mat, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.conj_ofReal] <;>
      field_simp [pb_bg_sqrt2_ne_zero] <;>
      rw [pb_bg_sqrt2_sq, Complex.I_sq] <;>
      ring
  have hunit' : pb_bg_gen0_mat * star pb_bg_gen0_mat = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pb_bg_gen0_mat, pb_bg_H_mat, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.conj_ofReal] <;>
      field_simp [pb_bg_sqrt2_ne_zero] <;>
      rw [pb_bg_sqrt2_sq, Complex.I_sq] <;>
      ring
  have hdet : pb_bg_gen0_mat.det = 1 := by
    rw [Matrix.det_fin_two]
    simp [pb_bg_gen0_mat, pb_bg_H_mat]
    field_simp [pb_bg_sqrt2_ne_zero]
    rw [pb_bg_sqrt2_sq]
    ring_nf
    rw [Complex.I_sq]
    ring
  exact ⟨⟨hunit, hunit'⟩, hdet⟩

private theorem pb_bg_gen1_mem_SU2 :
    pb_bg_gen1_mat ∈ SpectralGapConjecture.SU 2 := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  have hunit : star pb_bg_gen1_mat * pb_bg_gen1_mat = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pb_bg_gen1_mat, Matrix.mul_apply, Fin.sum_univ_two]
    · rw [← Complex.star_def, show -(Complex.I * ↑Real.pi) / 8 = -Complex.I * ↑Real.pi / 8 by ring,
        pb_bg_exp_pi8_conj, pb_bg_exp_pi8_neg_mul]
    · rw [← Complex.star_def, pb_bg_exp_pi8_conj', pb_bg_exp_pi8_mul_neg]
  have hunit' : pb_bg_gen1_mat * star pb_bg_gen1_mat = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pb_bg_gen1_mat, Matrix.mul_apply, Fin.sum_univ_two]
    · rw [← Complex.star_def, show -(Complex.I * ↑Real.pi) / 8 = -Complex.I * ↑Real.pi / 8 by ring,
        pb_bg_exp_pi8_conj, pb_bg_exp_pi8_mul_neg]
    · rw [← Complex.star_def, pb_bg_exp_pi8_conj', pb_bg_exp_pi8_neg_mul]
  have hdet : pb_bg_gen1_mat.det = 1 := by
    rw [Matrix.det_fin_two]
    simp [pb_bg_gen1_mat]
    rw [show -(Complex.I * ↑Real.pi) / 8 = -Complex.I * ↑Real.pi / 8 by ring, pb_bg_exp_pi8_mul_neg]
  exact ⟨⟨hunit, hunit'⟩, hdet⟩

noncomputable def pb_bg_gen : Fin 2 → SpectralGapConjecture.SU 2
  | 0 => ⟨pb_bg_gen0_mat, pb_bg_gen0_mem_SU2⟩
  | 1 => ⟨pb_bg_gen1_mat, pb_bg_gen1_mem_SU2⟩

/-! ### 2. Algebraicity -/

private theorem pb_bg_isAlgebraic_i_inv_sqrt2 :
    IsAlgebraic ℚ (Complex.I * (Real.sqrt 2 : ℂ)⁻¹) := by
  refine ⟨2 * Polynomial.X ^ 2 + 1, ?_, ?_⟩
  · intro h0
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 0) h0
    simp at hc
  · simp [map_add, map_mul, map_pow, map_ofNat, map_one, Polynomial.aeval_X]
    field_simp [pb_bg_sqrt2_ne_zero]
    rw [pb_bg_sqrt2_sq]
    ring_nf
    rw [Complex.I_sq]
    ring

private theorem pb_bg_isAlgebraic_neg_i_inv_sqrt2 :
    IsAlgebraic ℚ (-(Complex.I * (Real.sqrt 2 : ℂ)⁻¹)) :=
  pb_bg_isAlgebraic_i_inv_sqrt2.neg

private theorem pb_bg_isAlgebraic_exp_pi8 :
    IsAlgebraic ℚ (Complex.exp (Complex.I * Real.pi / 8)) := by
  refine ⟨Polynomial.X ^ 8 + 1, ?_, ?_⟩
  · intro h0
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 0) h0
    simp at hc
  · simp only [map_add, map_pow, map_one, Polynomial.aeval_X]
    rw [← Complex.exp_nat_mul]
    have harg : (8 : ℕ) * (Complex.I * Real.pi / 8) = Real.pi * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_pi_mul_I]
    ring

private theorem pb_bg_isAlgebraic_exp_neg_pi8 :
    IsAlgebraic ℚ (Complex.exp (-Complex.I * Real.pi / 8)) := by
  refine ⟨Polynomial.X ^ 8 + 1, ?_, ?_⟩
  · intro h0
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 0) h0
    simp at hc
  · simp only [map_add, map_pow, map_one, Polynomial.aeval_X]
    rw [← Complex.exp_nat_mul]
    have harg : (8 : ℕ) * (-Complex.I * Real.pi / 8) = -(Real.pi * Complex.I) := by
      push_cast; ring
    rw [harg, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

theorem pb_bg_halg : ∀ (j : Fin 2) (a b : Fin 2),
    IsAlgebraic ℚ ((pb_bg_gen j : Matrix (Fin 2) (Fin 2) ℂ) a b) := by
  intro j a b
  fin_cases j <;> fin_cases a <;> fin_cases b
  · simpa [pb_bg_gen, pb_bg_gen0_mat, pb_bg_H_mat] using pb_bg_isAlgebraic_i_inv_sqrt2
  · simpa [pb_bg_gen, pb_bg_gen0_mat, pb_bg_H_mat] using pb_bg_isAlgebraic_i_inv_sqrt2
  · simpa [pb_bg_gen, pb_bg_gen0_mat, pb_bg_H_mat] using pb_bg_isAlgebraic_i_inv_sqrt2
  · simpa [pb_bg_gen, pb_bg_gen0_mat, pb_bg_H_mat] using pb_bg_isAlgebraic_neg_i_inv_sqrt2
  · simpa [pb_bg_gen, pb_bg_gen1_mat] using pb_bg_isAlgebraic_exp_neg_pi8
  · simp [pb_bg_gen, pb_bg_gen1_mat]; exact isAlgebraic_zero
  · simp [pb_bg_gen, pb_bg_gen1_mat]; exact isAlgebraic_zero
  · simpa [pb_bg_gen, pb_bg_gen1_mat] using pb_bg_isAlgebraic_exp_pi8

/-! ### 3. Topological Density in `SU(2)` -/

private def pb_bg_toGate : SpectralGapConjecture.SU 2 →* QEC.Distillation.SingleQubitGate where
  toFun U := ⟨U.1, Matrix.specialUnitaryGroup_le_unitaryGroup U.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem pb_bg_toGate_inducing : Topology.IsInducing pb_bg_toGate := by
  refine Topology.IsInducing.subtypeVal.of_comp_iff.mp ?_
  exact Topology.IsInducing.subtypeVal

private def pb_bg_chebyshevSeq : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | k + 2 => pb_bg_chebyshevSeq (k + 1) - 16 * pb_bg_chebyshevSeq k

private theorem pb_bg_chebyshevSeq_odd (k : ℕ) (hk : 1 ≤ k) :
    pb_bg_chebyshevSeq k % 2 = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => omega
    | 1 => simp [pb_bg_chebyshevSeq]
    | 2 => simp [pb_bg_chebyshevSeq]
    | m + 3 =>
      have ih1 : pb_bg_chebyshevSeq (m + 2) % 2 = 1 := ih (m + 2) (by omega) (by omega)
      have hstep : pb_bg_chebyshevSeq (m + 3) =
          pb_bg_chebyshevSeq (m + 2) - 16 * pb_bg_chebyshevSeq (m + 1) :=
        pb_bg_chebyshevSeq.eq_3 (m + 1)
      rw [hstep]
      omega

private theorem pb_bg_chebyshevSeq_formula (φ : ℝ) (hcos : Real.cos φ = 1 / 8) (k : ℕ) :
    (pb_bg_chebyshevSeq k : ℝ) = (4 : ℝ) ^ k * (2 * Real.cos ((k : ℝ) * φ)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => simp [pb_bg_chebyshevSeq]
    | 1 =>
      simp [pb_bg_chebyshevSeq, hcos]
      norm_num
    | m + 2 =>
      have ih1 := ih (m + 1) (by omega)
      have ih2 := ih m (by omega)
      have htrig : Real.cos (((m + 2 : ℕ) : ℝ) * φ) + Real.cos ((m : ℝ) * φ) =
          2 * Real.cos (((m + 1 : ℕ) : ℝ) * φ) * Real.cos φ := by
        have h1 : (((m + 2 : ℕ) : ℝ) * φ) = (((m + 1 : ℕ) : ℝ) * φ) + φ := by
          push_cast; ring
        have h2 : ((m : ℝ) * φ) = (((m + 1 : ℕ) : ℝ) * φ) - φ := by
          push_cast; ring
        rw [h1, h2, Real.cos_add, Real.cos_sub]
        ring
      have hcos_step : 2 * Real.cos (((m + 2 : ℕ) : ℝ) * φ) =
          (1 / 4 : ℝ) * (2 * Real.cos (((m + 1 : ℕ) : ℝ) * φ)) - 2 * Real.cos ((m : ℝ) * φ) := by
        rw [hcos] at htrig
        linarith
      calc (pb_bg_chebyshevSeq (m + 2) : ℝ)
          = (pb_bg_chebyshevSeq (m + 1) : ℝ) - 16 * (pb_bg_chebyshevSeq m : ℝ) := by
              rw [pb_bg_chebyshevSeq]; push_cast; ring
        _ = (4 : ℝ) ^ (m + 1) * (2 * Real.cos (((m + 1 : ℕ) : ℝ) * φ)) -
              16 * ((4 : ℝ) ^ m * (2 * Real.cos ((m : ℝ) * φ))) := by rw [ih1, ih2]
        _ = (4 : ℝ) ^ (m + 2) * (2 * Real.cos (((m + 2 : ℕ) : ℝ) * φ)) := by
              rw [hcos_step]; ring

private theorem pb_bg_arccos_three_fourths_irrational :
    Irrational (Real.arccos (3 / 4 : ℝ) / (2 * Real.pi)) := by
  intro ⟨q, hq⟩
  set θ := Real.arccos (3 / 4 : ℝ)
  set φ := 2 * θ
  have hcosθ : Real.cos θ = 3 / 4 := Real.cos_arccos (by norm_num) (by norm_num)
  have hcosφ : Real.cos φ = 1 / 8 := by
    dsimp [φ]
    rw [Real.cos_two_mul, hcosθ]
    norm_num
  have hq' : θ / (2 * Real.pi) = (q.num : ℝ) / (q.den : ℝ) := by
    rw [← hq]
    exact_mod_cast (Rat.num_div_den q).symm
  have hb_pos : 0 < q.den := q.pos
  have hb_ne : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb_pos.ne'
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hθ_eq : (q.den : ℝ) * φ = ((2 * q.num : ℤ) : ℝ) * (2 * Real.pi) := by
    have hmul : θ = ((q.num : ℝ) / (q.den : ℝ)) * (2 * Real.pi) := by
      rw [← hq']
      field_simp [h2pi_ne]
    dsimp [φ]
    rw [hmul]
    push_cast
    field_simp [hb_ne]
  have hcos_bφ : Real.cos ((q.den : ℝ) * φ) = 1 := by
    rw [hθ_eq]
    exact Real.cos_int_mul_two_pi (2 * q.num)
  have hF_real : (pb_bg_chebyshevSeq q.den : ℝ) = ((2 * 4 ^ q.den : ℤ) : ℝ) := by
    rw [pb_bg_chebyshevSeq_formula φ hcosφ q.den, hcos_bφ]
    push_cast
    ring
  have hF_int : pb_bg_chebyshevSeq q.den = 2 * 4 ^ q.den := by
    exact_mod_cast hF_real
  have hodd : pb_bg_chebyshevSeq q.den % 2 = 1 := pb_bg_chebyshevSeq_odd q.den hb_pos
  rw [hF_int] at hodd
  omega

private theorem pb_bg_conj_z_su2Matrix (r : ℝ) (vx vy vz : ℝ) :
    !![-Complex.I, 0; 0, Complex.I] * QEC.Distillation.su2Matrix r ![vx, vy, vz] *
        !![Complex.I, 0; 0, -Complex.I] =
      QEC.Distillation.su2Matrix r ![-vx, -vy, vz] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QEC.Distillation.su2Matrix, QEC.Distillation.blochPauliMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;>
    ring_nf <;>
    simp [Complex.I_sq] <;>
    ring

private theorem pb_bg_cos_pi8_sq_add_sin :
    Real.cos (Real.pi / 8) ^ 2 + Real.sin (Real.pi / 8) ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq _

private theorem pb_bg_sin_pi8_mul_cos :
    Real.cos (Real.pi / 8) * Real.sin (Real.pi / 8) = 1 / (2 * Real.sqrt 2) := by
  have h : 2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) = Real.sin (Real.pi / 4) := by
    rw [show Real.pi / 4 = 2 * (Real.pi / 8) by ring, Real.sin_two_mul]
  rw [Real.sin_pi_div_four] at h
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  calc
    Real.cos (Real.pi / 8) * Real.sin (Real.pi / 8)
        = (2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8)) / 2 := by ring
    _ = (Real.sqrt 2 / 2) / 2 := by rw [h]
    _ = 1 / (2 * Real.sqrt 2) := by
      field_simp
      rw [Real.sq_sqrt (by norm_num)]

private theorem pb_bg_cos_pi8_pos : 0 < Real.cos (Real.pi / 8) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

private theorem pb_bg_sin_pi8_pos : 0 < Real.sin (Real.pi / 8) := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]

private theorem pb_bg_exp_pi8_eq_cos_sin :
    Complex.exp (Complex.I * Real.pi / 8) =
      (Real.cos (Real.pi / 8) : ℂ) + Complex.I * (Real.sin (Real.pi / 8) : ℂ) := by
  rw [show Complex.I * Real.pi / 8 = ((Real.pi / 8 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

private theorem pb_bg_exp_neg_pi8_eq_cos_sin :
    Complex.exp (-Complex.I * Real.pi / 8) =
      (Real.cos (Real.pi / 8) : ℂ) - Complex.I * (Real.sin (Real.pi / 8) : ℂ) := by
  rw [show -Complex.I * Real.pi / 8 = ((-(Real.pi / 8) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

private theorem pb_bg_t_matrix :
    (pb_bg_toGate (pb_bg_gen 1) : Matrix (Fin 2) (Fin 2) ℂ) =
      QEC.Distillation.su2Matrix (Real.cos (Real.pi / 8)) ![0, 0, Real.sin (Real.pi / 8)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [pb_bg_toGate, pb_bg_gen, pb_bg_gen1_mat, QEC.Distillation.su2Matrix,
      QEC.Distillation.blochPauliMatrix]
  · rw [pb_bg_exp_neg_pi8_eq_cos_sin]; simp
  · simp
  · simp
  · rw [pb_bg_exp_pi8_eq_cos_sin]; simp

private theorem pb_bg_h_inv_matrix :
    (((pb_bg_toGate (pb_bg_gen 0))⁻¹ : QEC.Distillation.SingleQubitGate) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      (-Complex.I) • pb_bg_H_mat := by
  change star (pb_bg_toGate (pb_bg_gen 0) : Matrix (Fin 2) (Fin 2) ℂ) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pb_bg_toGate, pb_bg_gen, pb_bg_gen0_mat, pb_bg_H_mat, Complex.conj_ofReal]

private theorem pb_bg_hth_matrix :
    ((pb_bg_toGate (pb_bg_gen 0) * pb_bg_toGate (pb_bg_gen 1) *
        (pb_bg_toGate (pb_bg_gen 0))⁻¹ : QEC.Distillation.SingleQubitGate) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      QEC.Distillation.su2Matrix (Real.cos (Real.pi / 8)) ![Real.sin (Real.pi / 8), 0, 0] := by
  rw [Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.mul_val, pb_bg_h_inv_matrix]
  change pb_bg_gen0_mat * pb_bg_gen1_mat * ((-Complex.I) • pb_bg_H_mat) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pb_bg_gen0_mat, pb_bg_gen1_mat, pb_bg_H_mat, QEC.Distillation.su2Matrix,
      QEC.Distillation.blochPauliMatrix, pb_bg_exp_pi8_eq_cos_sin, pb_bg_exp_neg_pi8_eq_cos_sin,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Complex.ofReal_zero] <;>
    norm_num <;>
    field_simp [pb_bg_sqrt2_ne_zero] <;>
    rw [pb_bg_sqrt2_sq] <;>
    ring_nf <;>
    simp [Complex.I_sq]

private theorem pb_bg_z_matrix :
    ((pb_bg_toGate (pb_bg_gen 1) ^ 4 : QEC.Distillation.SingleQubitGate) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      !![-Complex.I, 0; 0, Complex.I] := by
  have hp : ((pb_bg_toGate (pb_bg_gen 1) ^ 4 : QEC.Distillation.SingleQubitGate) :
      Matrix (Fin 2) (Fin 2) ℂ) =
      (pb_bg_gen1_mat) ^ 4 := by
    simp [pb_bg_toGate, pb_bg_gen]
  rw [hp, pow_succ, pow_succ, pow_succ, pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pb_bg_gen1_mat, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    have harg : -(Complex.I * Real.pi) / 8 + -(Complex.I * Real.pi) / 8 +
        -(Complex.I * Real.pi) / 8 + -(Complex.I * Real.pi) / 8 =
        ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I]
    simp
  · rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    have harg : Complex.I * Real.pi / 8 + Complex.I * Real.pi / 8 +
        Complex.I * Real.pi / 8 + Complex.I * Real.pi / 8 =
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I]
    simp

private theorem pb_bg_z_inv_matrix :
    (((pb_bg_toGate (pb_bg_gen 1) ^ 4)⁻¹ : QEC.Distillation.SingleQubitGate) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.I, 0; 0, -Complex.I] := by
  change star ((pb_bg_toGate (pb_bg_gen 1) ^ 4 : QEC.Distillation.SingleQubitGate) :
      Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [pb_bg_z_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem pb_bg_hdense :
    Dense ((Subgroup.closure (Set.range pb_bg_gen) : Subgroup (SpectralGapConjecture.SU 2)) :
      Set (SpectralGapConjecture.SU 2)) := by
  let gens : Set QEC.Distillation.SingleQubitGate :=
    Set.range (fun j => pb_bg_toGate (pb_bg_gen j))
  let h : QEC.Distillation.SingleQubitGate := pb_bg_toGate (pb_bg_gen 0)
  let t : QEC.Distillation.SingleQubitGate := pb_bg_toGate (pb_bg_gen 1)
  have hh_mem : h ∈ QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup gens :=
    Subgroup.subset_closure ⟨0, rfl⟩
  have ht_mem : t ∈ QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup gens :=
    Subgroup.subset_closure ⟨1, rfl⟩
  let A : QEC.Distillation.SingleQubitGate := t * (h * t * h⁻¹)
  let z_gate : QEC.Distillation.SingleQubitGate := t ^ 4
  let W : QEC.Distillation.SingleQubitGate := A * (z_gate * A * z_gate⁻¹)
  let W' : QEC.Distillation.SingleQubitGate := z_gate * W * z_gate⁻¹
  have hA_mem : A ∈ QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup gens :=
    mul_mem ht_mem (mul_mem (mul_mem hh_mem ht_mem) (inv_mem hh_mem))
  have hz_mem : z_gate ∈ QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup gens :=
    pow_mem ht_mem 4
  have hW_mem : W ∈ QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup gens :=
    mul_mem hA_mem (mul_mem (mul_mem hz_mem hA_mem) (inv_mem hz_mem))
  have hW'_mem : W' ∈ QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup gens :=
    mul_mem (mul_mem hz_mem hW_mem) (inv_mem hz_mem)
  set c := Real.cos (Real.pi / 8)
  set s := Real.sin (Real.pi / 8)
  have hcs_sq : c ^ 2 + s ^ 2 = 1 := pb_bg_cos_pi8_sq_add_sin
  have hcs_prod : c * s = 1 / (2 * Real.sqrt 2) := pb_bg_sin_pi8_mul_cos
  have hcs_prod_sq : c ^ 2 * s ^ 2 = 1 / 8 := by
    calc
      c ^ 2 * s ^ 2 = (c * s) ^ 2 := by ring
      _ = (1 / (2 * Real.sqrt 2)) ^ 2 := by rw [hcs_prod]
      _ = 1 / 8 := by
        field_simp
        rw [Real.sq_sqrt (by norm_num)]
        norm_num
  have hA_mat : (A : Matrix (Fin 2) (Fin 2) ℂ) =
      QEC.Distillation.su2Matrix (c ^ 2) ![c * s, s ^ 2, c * s] := by
    change (t : Matrix (Fin 2) (Fin 2) ℂ) *
      ((h * t * h⁻¹ : QEC.Distillation.SingleQubitGate) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [pb_bg_t_matrix, pb_bg_hth_matrix, QEC.Distillation.su2Matrix_mul]
    congr 1
    · simp [c]; ring
    · ext i
      fin_cases i <;>
        simp [QEC.Distillation.su2VectorProduct, cross_apply, c, s]; ring
  have hzAz_mat : ((z_gate * A * z_gate⁻¹ : QEC.Distillation.SingleQubitGate) :
      Matrix (Fin 2) (Fin 2) ℂ) =
      QEC.Distillation.su2Matrix (c ^ 2) ![-(c * s), -(s ^ 2), c * s] := by
    rw [Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.mul_val,
      pb_bg_z_matrix, pb_bg_z_inv_matrix, hA_mat]
    exact pb_bg_conj_z_su2Matrix (c ^ 2) (c * s) (s ^ 2) (c * s)
  let vW : Fin 3 → ℝ := ![2 * c * s ^ 3, -2 * c ^ 2 * s ^ 2, 2 * c ^ 3 * s]
  have hW_mat : (W : Matrix (Fin 2) (Fin 2) ℂ) =
      QEC.Distillation.su2Matrix (3 / 4 : ℝ) vW := by
    change (A : Matrix (Fin 2) (Fin 2) ℂ) *
      ((z_gate * A * z_gate⁻¹ : QEC.Distillation.SingleQubitGate) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [hA_mat, hzAz_mat, QEC.Distillation.su2Matrix_mul]
    have hscal : c ^ 2 * c ^ 2 -
        ![c * s, s ^ 2, c * s] ⬝ᵥ ![-(c * s), -(s ^ 2), c * s] = 3 / 4 := by
      simp
      nlinarith [hcs_sq, hcs_prod_sq]
    have hvec : QEC.Distillation.su2VectorProduct (c ^ 2) (c ^ 2)
        ![c * s, s ^ 2, c * s] ![-(c * s), -(s ^ 2), c * s] = vW := by
      ext i
      fin_cases i <;>
        simp [QEC.Distillation.su2VectorProduct, cross_apply, vW] <;>
        ring
    rw [hscal, hvec]
  have hvW_norm : vW ⬝ᵥ vW = 7 / 16 := by
    simp [vW]
    have h1 : c ^ 4 + c ^ 2 * s ^ 2 + s ^ 4 = 7 / 8 := by
      nlinarith [hcs_sq, hcs_prod_sq]
    nlinarith [hcs_prod_sq, h1]
  have hvW_nz : vW ⬝ᵥ vW ≠ 0 := by
    rw [hvW_norm]
    norm_num
  let axis : QEC.Distillation.UnitBlochAxis := QEC.Distillation.normalizedBlochAxis vW hvW_nz
  let θ : ℝ := Real.arccos (3 / 4 : ℝ)
  have hcosθ : Real.cos θ = 3 / 4 := Real.cos_arccos (by norm_num) (by norm_num)
  have hsinθ : Real.sin θ = Real.sqrt (vW ⬝ᵥ vW) := by
    dsimp [θ]
    rw [Real.sin_arccos, hvW_norm]
    norm_num
  have hW_eq_axis : W = QEC.Distillation.axisCircle axis (θ : AddCircle (2 * Real.pi)) := by
    apply Subtype.ext
    change (W : Matrix (Fin 2) (Fin 2) ℂ) =
      ((QEC.Distillation.axisCircleRealSU axis θ : QEC.Distillation.SingleQubitGate) :
        Matrix (Fin 2) (Fin 2) ℂ)
    rw [hW_mat, QEC.Distillation.axisCircleRealSU_matrix, hcosθ, hsinθ]
    congr 1
    exact (QEC.Distillation.sqrt_smul_blochVector_normalizedBlochAxis vW hvW_nz).symm
  let axis' : QEC.Distillation.UnitBlochAxis :=
    ⟨-axis.x, -axis.y, axis.z, by linear_combination axis.norm_sq⟩
  have hW'_mat : (W' : Matrix (Fin 2) (Fin 2) ℂ) =
      QEC.Distillation.su2Matrix (3 / 4 : ℝ) ![-vW 0, -vW 1, vW 2] := by
    change ((z_gate * W * z_gate⁻¹ : QEC.Distillation.SingleQubitGate) :
      Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.mul_val,
      pb_bg_z_matrix, pb_bg_z_inv_matrix, hW_mat]
    exact pb_bg_conj_z_su2Matrix (3 / 4 : ℝ) (vW 0) (vW 1) (vW 2)
  have hW'_eq_axis' : W' = QEC.Distillation.axisCircle axis' (θ : AddCircle (2 * Real.pi)) := by
    apply Subtype.ext
    change (W' : Matrix (Fin 2) (Fin 2) ℂ) =
      ((QEC.Distillation.axisCircleRealSU axis' θ : QEC.Distillation.SingleQubitGate) :
        Matrix (Fin 2) (Fin 2) ℂ)
    rw [hW'_mat, QEC.Distillation.axisCircleRealSU_matrix, hcosθ, hsinθ]
    congr 1
    have hscale := QEC.Distillation.sqrt_smul_blochVector_normalizedBlochAxis vW hvW_nz
    ext i
    have hi0 := congrFun hscale 0
    have hi1 := congrFun hscale 1
    have hi2 := congrFun hscale 2
    fin_cases i
    · simpa [axis, axis', QEC.Distillation.blochVector] using (congrArg Neg.neg hi0).symm
    · simpa [axis, axis', QEC.Distillation.blochVector] using (congrArg Neg.neg hi1).symm
    · simpa [axis, axis', QEC.Distillation.blochVector] using hi2.symm
  have hnonparallel : axis.Nonparallel axis' := by
    dsimp [QEC.Distillation.UnitBlochAxis.Nonparallel, QEC.Distillation.blochCrossSq]
    have hcross : (axis.y * axis'.z - axis.z * axis'.y) ^ 2 +
        (axis.z * axis'.x - axis.x * axis'.z) ^ 2 +
        (axis.x * axis'.y - axis.y * axis'.x) ^ 2 =
        4 * (axis.x ^ 2 + axis.y ^ 2) * axis.z ^ 2 := by
      dsimp [axis']
      ring
    rw [hcross]
    have hm_pos : 0 < Real.sqrt (vW ⬝ᵥ vW) := by
      rw [hvW_norm]
      positivity
    have hy_ne : axis.y ≠ 0 := by
      dsimp [axis, QEC.Distillation.normalizedBlochAxis, vW]
      apply div_ne_zero _ hm_pos.ne'
      nlinarith [hcs_prod_sq]
    have hz_ne : axis.z ≠ 0 := by
      dsimp [axis, QEC.Distillation.normalizedBlochAxis, vW]
      apply div_ne_zero _ hm_pos.ne'
      have hc_pos : 0 < c := pb_bg_cos_pi8_pos
      have hs_pos : 0 < s := pb_bg_sin_pi8_pos
      positivity
    have hy_sq_pos : 0 < axis.y ^ 2 := sq_pos_of_ne_zero hy_ne
    have hz_sq_pos : 0 < axis.z ^ 2 := sq_pos_of_ne_zero hz_ne
    have hx_sq_nonneg : 0 ≤ axis.x ^ 2 := sq_nonneg _
    nlinarith
  have hirr : Irrational (θ / (2 * Real.pi)) := pb_bg_arccos_three_fourths_irrational
  have hcircle1 : ∀ t : AddCircle (2 * Real.pi),
      QEC.Distillation.axisCircleSU axis t ∈
        QEC.Distillation.specialUnitaryGeneratedClosure gens :=
    QEC.Distillation.axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
      gens axis θ W hW_mem hW_eq_axis hirr
  have hcircle2 : ∀ t : AddCircle (2 * Real.pi),
      QEC.Distillation.axisCircleSU axis' t ∈
        QEC.Distillation.specialUnitaryGeneratedClosure gens :=
    QEC.Distillation.axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
      gens axis' θ W' hW'_mem hW'_eq_axis' hirr
  have hK_top : QEC.Distillation.specialUnitaryGeneratedClosure gens = ⊤ :=
    QEC.Distillation.closedSubgroup_eq_top_of_contains_nonparallel_axisCircles
      (QEC.Distillation.specialUnitaryGeneratedClosure gens)
      (QEC.Distillation.isClosed_specialUnitaryGeneratedClosure gens)
      axis axis' hnonparallel hcircle1 hcircle2
  rw [dense_iff_closure_eq]
  ext U
  simp only [Set.mem_univ, iff_true]
  let U_su : QEC.Distillation.SingleQubitSpecialUnitary :=
    ⟨pb_bg_toGate U, U.2.2⟩
  have hU_mem : U_su ∈ QEC.Distillation.specialUnitaryGeneratedClosure gens := by
    rw [hK_top]
    trivial
  have hU_closure : (U_su : QEC.Distillation.SingleQubitGate) ∈
      QEC.Distillation.GeneratedUniversality.generatedUnitaryTopologicalClosure gens :=
    (QEC.Distillation.mem_specialUnitaryGeneratedClosure_iff gens U_su).mp hU_mem
  have himg_eq : pb_bg_toGate ''
      ((Subgroup.closure (Set.range pb_bg_gen) : Subgroup (SpectralGapConjecture.SU 2)) :
        Set (SpectralGapConjecture.SU 2)) =
      (QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup gens :
        Set QEC.Distillation.SingleQubitGate) := by
    have hgens_eq : gens = pb_bg_toGate '' Set.range pb_bg_gen := by
      ext x
      simp [gens]
    rw [QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup, hgens_eq,
      ← MonoidHom.map_closure, Subgroup.coe_map]
  change U ∈ closure ((Subgroup.closure (Set.range pb_bg_gen) :
      Subgroup (SpectralGapConjecture.SU 2)) : Set (SpectralGapConjecture.SU 2))
  rw [pb_bg_toGate_inducing.closure_eq_preimage_closure_image]
  change pb_bg_toGate U ∈ closure (pb_bg_toGate ''
      ((Subgroup.closure (Set.range pb_bg_gen) : Subgroup (SpectralGapConjecture.SU 2)) :
        Set (SpectralGapConjecture.SU 2)))
  rw [himg_eq]
  exact hU_closure

/-! ### 4. Word-to-`Circuit CliffordT 1` Realization -/

private theorem pb_bg_hadamard_mem_CliffordT :
    QAlgorithms.Gate.ofMatrix1 QAlgorithms.hadamard ∈ ConstOverheadCompile.Main.CliffordT := by
  simp [ConstOverheadCompile.Main.CliffordT]

private theorem pb_bg_gateT_mem_CliffordT :
    QAlgorithms.Gate.ofMatrix1 QAlgorithms.gateT ∈ ConstOverheadCompile.Main.CliffordT := by
  simp [ConstOverheadCompile.Main.CliffordT]

private noncomputable def pb_bg_H_app : QAlgorithms.GateApp ConstOverheadCompile.Main.CliffordT 1 :=
  ⟨QAlgorithms.Gate.ofMatrix1 QAlgorithms.hadamard, pb_bg_hadamard_mem_CliffordT,
    Function.Embedding.refl _⟩

private noncomputable def pb_bg_T_app : QAlgorithms.GateApp ConstOverheadCompile.Main.CliffordT 1 :=
  ⟨QAlgorithms.Gate.ofMatrix1 QAlgorithms.gateT, pb_bg_gateT_mem_CliffordT,
    Function.Embedding.refl _⟩

private theorem pb_bg_submatrix_fin2_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (A * B).submatrix pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm =
      A.submatrix pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm *
        B.submatrix pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm := by
  ext y z
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Equiv.sum_comp pb_bg_fin2EquivQubits1.symm fun k =>
    A (pb_bg_fin2EquivQubits1.symm y) k * B k (pb_bg_fin2EquivQubits1.symm z)).symm

private theorem pb_bg_circuit_append_unitary
    (c1 c2 : QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1) :
    QAlgorithms.Circuit.unitary (c1 ++ c2) =
      QAlgorithms.Circuit.unitary c2 * QAlgorithms.Circuit.unitary c1 := by
  simp [QAlgorithms.Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

private theorem pb_bg_H_circuit_unitary :
    QAlgorithms.Circuit.unitary ([pb_bg_H_app] :
        QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1) =
      pb_bg_H_mat.submatrix pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm := by
  simp only [QAlgorithms.Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
  ext y z
  unfold QAlgorithms.embedOp pb_bg_H_app QAlgorithms.Gate.ofMatrix1
  rw [Matrix.of_apply, if_pos (fun a ha => absurd ⟨a, rfl⟩ ha)]
  simp only [Matrix.submatrix_apply, pb_bg_fin2EquivQubits1, Equiv.coe_fn_symm_mk]
  cases hy : y 0 <;> cases hz : z 0 <;>
    simp [hy, hz, QAlgorithms.hadamard, pb_bg_H_mat]

private theorem pb_bg_T_mat_eq :
    QAlgorithms.Circuit.unitary ([pb_bg_T_app] :
        QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1) =
      (!![1, 0; 0, Complex.exp (Complex.I * Real.pi / 4)] : Matrix (Fin 2) (Fin 2) ℂ).submatrix
        pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm := by
  simp only [QAlgorithms.Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
  ext y z
  unfold QAlgorithms.embedOp pb_bg_T_app QAlgorithms.Gate.ofMatrix1
  rw [Matrix.of_apply, if_pos (fun a ha => absurd ⟨a, rfl⟩ ha)]
  simp only [Matrix.submatrix_apply, pb_bg_fin2EquivQubits1, Equiv.coe_fn_symm_mk]
  cases hy : y 0 <;> cases hz : z 0 <;>
    simp [hy, hz, QAlgorithms.gateT]

private theorem pb_bg_step_to_circuit (p : Bool × Fin 2) :
    ∃ (c : QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1) (θ : ℝ),
      c.size ≤ 7 ∧
      (((if p.1 then pb_bg_gen p.2 else (pb_bg_gen p.2)⁻¹) : SpectralGapConjecture.SU 2) :
          Matrix (Fin 2) (Fin 2) ℂ).submatrix
          pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm =
        Complex.exp (θ * Complex.I) • c.unitary := by
  rcases p with ⟨b, j⟩
  cases b <;> fin_cases j
  · refine ⟨[pb_bg_H_app], -Real.pi / 2, by simp [QAlgorithms.Circuit.size], ?_⟩
    change (((pb_bg_gen 0)⁻¹ : SpectralGapConjecture.SU 2) : Matrix (Fin 2) (Fin 2) ℂ).submatrix
        pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm =
      Complex.exp ((-Real.pi / 2 : ℝ) * Complex.I) •
        QAlgorithms.Circuit.unitary ([pb_bg_H_app] :
          QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1)
    rw [pb_bg_H_circuit_unitary]
    have hinv : (((pb_bg_gen 0)⁻¹ : SpectralGapConjecture.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) =
        (-Complex.I) • pb_bg_H_mat := by
      change star (pb_bg_gen0_mat) = (-Complex.I) • pb_bg_H_mat
      ext a c
      fin_cases a <;> fin_cases c <;>
        simp [pb_bg_gen0_mat, pb_bg_H_mat, Complex.conj_ofReal]
    rw [hinv, Matrix.submatrix_smul]
    rw [show ((-Real.pi / 2 : ℝ) : ℂ) * Complex.I = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    simp
  · refine ⟨List.replicate 7 pb_bg_T_app, Real.pi / 8, by simp [QAlgorithms.Circuit.size], ?_⟩
    change (((pb_bg_gen 1)⁻¹ : SpectralGapConjecture.SU 2) : Matrix (Fin 2) (Fin 2) ℂ).submatrix
        pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm =
      Complex.exp ((Real.pi / 8 : ℝ) * Complex.I) •
        QAlgorithms.Circuit.unitary (List.replicate 7 pb_bg_T_app :
          QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1)
    have hrep : QAlgorithms.Circuit.unitary (List.replicate 7 pb_bg_T_app :
        QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1) =
        QAlgorithms.Circuit.unitary ([pb_bg_T_app] :
          QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1) ^ 7 := by
      have h1 : ∀ n : ℕ, QAlgorithms.Circuit.unitary (List.replicate n pb_bg_T_app :
          QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1) =
          QAlgorithms.Circuit.unitary ([pb_bg_T_app] :
            QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1) ^ n := by
        intro n
        induction n with
        | zero => simp [QAlgorithms.Circuit.unitary]
        | succ n ih =>
          rw [List.replicate_succ, ← List.singleton_append, pb_bg_circuit_append_unitary, ih,
            pow_succ]
      exact h1 7
    rw [hrep, pb_bg_T_mat_eq]
    have hpow : (!![1, 0; 0, Complex.exp (Complex.I * Real.pi / 4)] : Matrix (Fin 2) (Fin 2) ℂ).submatrix
        pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm ^ 7 =
        ((!![1, 0; 0, Complex.exp (Complex.I * Real.pi / 4)] :
            Matrix (Fin 2) (Fin 2) ℂ) ^ 7).submatrix
          pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm := by
      simp only [pow_succ, pow_zero, one_mul, ← pb_bg_submatrix_fin2_mul]
    rw [hpow]
    have hmat : (((pb_bg_gen 1)⁻¹ : SpectralGapConjecture.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) =
        Complex.exp ((Real.pi / 8 : ℝ) * Complex.I) •
          ((!![1, 0; 0, Complex.exp (Complex.I * Real.pi / 4)] :
            Matrix (Fin 2) (Fin 2) ℂ) ^ 7) := by
      have hinv : (((pb_bg_gen 1)⁻¹ : SpectralGapConjecture.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) =
          !![Complex.exp (Complex.I * Real.pi / 8), 0;
             0, Complex.exp (-Complex.I * Real.pi / 8)] := by
        change star (pb_bg_gen1_mat) = _
        ext a c
        fin_cases a <;> fin_cases c <;>
          simp [pb_bg_gen1_mat]
        · rw [← Complex.star_def, show -(Complex.I * ↑Real.pi) / 8 = -Complex.I * ↑Real.pi / 8 by ring,
            pb_bg_exp_pi8_conj]
        · rw [← Complex.star_def, pb_bg_exp_pi8_conj']; congr 1; ring
      rw [hinv]
      ext a c
      fin_cases a <;> fin_cases c <;>
        simp [pow_succ]
      · congr 1; ring
      · rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
          ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
        have harg : (Real.pi : ℂ) / 8 * Complex.I +
            (Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4 +
             Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4 +
             Complex.I * Real.pi / 4) =
            -Complex.I * Real.pi / 8 + 2 * Real.pi * Complex.I := by
          ring
        rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
        congr 1; ring
    rw [hmat, Matrix.submatrix_smul]
    rfl
  · refine ⟨[pb_bg_H_app], Real.pi / 2, by simp [QAlgorithms.Circuit.size], ?_⟩
    change (pb_bg_gen0_mat).submatrix pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm =
      Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) •
        QAlgorithms.Circuit.unitary ([pb_bg_H_app] :
          QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1)
    rw [pb_bg_H_circuit_unitary]
    rw [pb_bg_gen0_mat, Matrix.submatrix_smul]
    rw [Complex.exp_mul_I]
    simp
  · refine ⟨[pb_bg_T_app], -Real.pi / 8, by simp [QAlgorithms.Circuit.size], ?_⟩
    change (pb_bg_gen1_mat).submatrix pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm =
      Complex.exp ((-Real.pi / 8 : ℝ) * Complex.I) •
        QAlgorithms.Circuit.unitary ([pb_bg_T_app] :
          QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1)
    rw [pb_bg_T_mat_eq]
    have hmat : pb_bg_gen1_mat =
        Complex.exp ((-Real.pi / 8 : ℝ) * Complex.I) •
          (!![1, 0; 0, Complex.exp (Complex.I * Real.pi / 4)] : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext a c
      fin_cases a <;> fin_cases c <;> simp [pb_bg_gen1_mat]
      · congr 1; ring
      · rw [← Complex.exp_add]
        congr 1; ring
    rw [hmat, Matrix.submatrix_smul]
    rfl

theorem pb_bg_word_to_circuit (w : List (Bool × Fin 2)) :
    ∃ (c : QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1) (θ : ℝ),
      c.size ≤ 7 * w.length ∧
      (((w.map fun p => if p.1 then pb_bg_gen p.2 else (pb_bg_gen p.2)⁻¹).prod :
          SpectralGapConjecture.SU 2) : Matrix (Fin 2) (Fin 2) ℂ).submatrix
          pb_bg_fin2EquivQubits1.symm pb_bg_fin2EquivQubits1.symm =
        Complex.exp (θ * Complex.I) • c.unitary := by
  induction w with
  | nil =>
    refine ⟨[], 0, by simp [QAlgorithms.Circuit.size], ?_⟩
    simp only [List.map_nil, List.prod_nil, OneMemClass.coe_one]
    ext y z
    simp [QAlgorithms.Circuit.unitary, Matrix.one_apply]
  | cons p rest ih =>
    rcases pb_bg_step_to_circuit p with ⟨c1, θ1, hc1_size, hc1_u⟩
    rcases ih with ⟨c2, θ2, hc2_size, hc2_u⟩
    refine ⟨c2 ++ c1, θ1 + θ2, ?_, ?_⟩
    · simp only [QAlgorithms.Circuit.size, List.length_append, List.length_cons]
      have : c2.length + c1.length ≤ 7 * rest.length + 7 := Nat.add_le_add hc2_size hc1_size
      omega
    · simp only [List.map_cons, List.prod_cons]
      rw [show ((((if p.1 then pb_bg_gen p.2 else (pb_bg_gen p.2)⁻¹) *
          (rest.map fun p => if p.1 then pb_bg_gen p.2 else (pb_bg_gen p.2)⁻¹).prod :
            SpectralGapConjecture.SU 2) : Matrix (Fin 2) (Fin 2) ℂ)) =
          (((if p.1 then pb_bg_gen p.2 else (pb_bg_gen p.2)⁻¹) : SpectralGapConjecture.SU 2) :
            Matrix (Fin 2) (Fin 2) ℂ) *
          (((rest.map fun p => if p.1 then pb_bg_gen p.2 else (pb_bg_gen p.2)⁻¹).prod :
            SpectralGapConjecture.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) from rfl]
      rw [pb_bg_submatrix_fin2_mul, hc1_u, hc2_u, pb_bg_circuit_append_unitary]
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, ← Complex.exp_add]
      congr 2
      push_cast
      ring


section PB_HRC_RS

open MeasureTheory SpectralGapConjecture QAlgorithms ConstOverheadCompile.Main
open scoped Matrix

/-! ### 1. Spectral norm and 2×2 Frobenius helpers -/

private lemma pb_rs_specNorm_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℂ) (A : Matrix ι ι ℂ) :
    specNorm (a • A) = ‖a‖ * specNorm A := by
  let _inst1 : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.instL2OpNormedAddCommGroup
  let _inst2 : NormedSpace ℂ (Matrix ι ι ℂ) := Matrix.instL2OpNormedSpace
  exact norm_smul a A

private lemma pb_rs_specNorm_neg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    specNorm (-A) = specNorm A := by
  let _inst1 : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.instL2OpNormedAddCommGroup
  exact norm_neg A

private lemma pb_rs_specNorm_add_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    specNorm (A + B) ≤ specNorm A + specNorm B := by
  let _inst1 : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.instL2OpNormedAddCommGroup
  exact norm_add_le A B

private lemma pb_rs_specNorm_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    specNorm (A - B) ≤ specNorm A + specNorm B := by
  let _inst1 : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.instL2OpNormedAddCommGroup
  exact norm_sub_le A B

private lemma pb_rs_specNorm_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    specNorm (A * B) ≤ specNorm A * specNorm B := by
  let _inst1 : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.instL2OpNormedAddCommGroup
  exact Matrix.l2_opNorm_mul A B

private lemma pb_rs_specNorm_unitary_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    specNorm U ≤ 1 := by
  let _inst1 : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.instL2OpNormedAddCommGroup
  rw [specNorm, ← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  change ‖act U x‖ ≤ ‖x‖
  exact (act_norm_of_mem_unitaryGroup hU x).le

private lemma pb_rs_specNorm_le_sqrt_sum_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    specNorm A ≤ Real.sqrt (∑ i : ι, ∑ j : ι, ‖A i j‖ ^ 2) := by
  let _inst1 : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.instL2OpNormedAddCommGroup
  rw [specNorm, ← Matrix.l2_opNorm_toEuclideanCLM]
  set S : ℝ := ∑ i : ι, ∑ j : ι, ‖A i j‖ ^ 2
  have hS_nonneg : 0 ≤ S :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg S) fun x => ?_
  have hsq : ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A x‖ ^ 2 ≤ (Real.sqrt S * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hrow : ∀ i : ι,
        ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A x) i‖ ^ 2 ≤
          (∑ j : ι, ‖A i j‖ ^ 2) * ‖x‖ ^ 2 := by
      intro i
      have htri : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A x) i‖ ≤
          ∑ j : ι, ‖A i j‖ * ‖x j‖ := by
        change ‖∑ j : ι, A i j * x j‖ ≤ _
        calc ‖∑ j : ι, A i j * x j‖
            ≤ ∑ j : ι, ‖A i j * x j‖ := norm_sum_le _ _
          _ = ∑ j : ι, ‖A i j‖ * ‖x j‖ := by
              refine Finset.sum_congr rfl fun j _ => norm_mul _ _
      have hsq1 : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A x) i‖ ^ 2 ≤
          (∑ j : ι, ‖A i j‖ * ‖x j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      have hcs : (∑ j : ι, ‖A i j‖ * ‖x j‖) ^ 2 ≤
          (∑ j : ι, ‖A i j‖ ^ 2) * (∑ j : ι, ‖x j‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖x j‖)
      rw [← EuclideanSpace.norm_sq_eq x] at hcs
      exact hsq1.trans hcs
    calc ∑ i : ι, ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A x) i‖ ^ 2
        ≤ ∑ i : ι, (∑ j : ι, ‖A i j‖ ^ 2) * ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => hrow i
      _ = S * ‖x‖ ^ 2 := by rw [← Finset.sum_mul]
      _ = (Real.sqrt S * ‖x‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hS_nonneg]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq

private lemma pb_rs_specNorm_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix κ κ ℂ) :
    specNorm (A.submatrix e e) ≤ specNorm A := by
  let _inst1 : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.instL2OpNormedAddCommGroup
  let _inst2 : NormedAddCommGroup (Matrix κ κ ℂ) := Matrix.instL2OpNormedAddCommGroup
  rw [specNorm, ← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (by
    rw [specNorm, ← Matrix.l2_opNorm_toEuclideanCLM]
    exact norm_nonneg _) fun x => ?_
  let y : EuclideanSpace ℂ κ := WithLp.toLp 2 (fun k => x (e.symm k))
  have hy_norm : ‖y‖ = ‖x‖ := by
    have hsq : ‖y‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      exact Fintype.sum_equiv e.symm _ _ fun k => rfl
    exact (sq_eq_sq₀ (norm_nonneg y) (norm_nonneg x)).mp hsq
  have hact : ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (A.submatrix e e) x‖ =
      ‖Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) A y‖ := by
    have hsq : ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (A.submatrix e e) x‖ ^ 2 =
        ‖Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) A y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      refine Fintype.sum_equiv e _ _ fun i => ?_
      change ‖∑ j : ι, A (e i) (e j) * x j‖ ^ 2 = ‖∑ k : κ, A (e i) k * x (e.symm k)‖ ^ 2
      congr 2
      refine Fintype.sum_equiv e _ _ fun j => ?_
      simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  rw [hact, ← hy_norm]
  change ‖Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) A y‖ ≤ specNorm A * ‖y‖
  rw [specNorm, ← Matrix.l2_opNorm_toEuclideanCLM]
  exact (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) A).le_opNorm y

private noncomputable def pb_rs_frobSq (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, ‖A i j‖ ^ 2

private lemma pb_rs_frobSq_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ pb_rs_frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma pb_rs_frobSq_conjTranspose (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pb_rs_frobSq Aᴴ = pb_rs_frobSq A := by
  unfold pb_rs_frobSq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.conjTranspose_apply]

private lemma pb_rs_frobSq_mul_unitary_left {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pb_rs_frobSq (U * A) = pb_rs_frobSq A := by
  unfold pb_rs_frobSq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖A i j‖ ^ 2)]
  refine Finset.sum_congr rfl fun j _ => ?_
  let v : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 (fun i => A i j)
  have hv : ‖act U v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [act_norm_of_mem_unitaryGroup hU v]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hv
  simpa [act, v, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hv

private lemma pb_rs_frobSq_mul_unitary_right {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pb_rs_frobSq (A * U) = pb_rs_frobSq A := by
  have hUs : Uᴴ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  calc pb_rs_frobSq (A * U)
      = pb_rs_frobSq (A * U)ᴴ := (pb_rs_frobSq_conjTranspose _).symm
    _ = pb_rs_frobSq (Uᴴ * Aᴴ) := by rw [Matrix.conjTranspose_mul]
    _ = pb_rs_frobSq Aᴴ := pb_rs_frobSq_mul_unitary_left hUs Aᴴ
    _ = pb_rs_frobSq A := pb_rs_frobSq_conjTranspose A

private lemma pb_rs_frobSq_add_le (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    pb_rs_frobSq (A + B) ≤ 2 * pb_rs_frobSq A + 2 * pb_rs_frobSq B := by
  unfold pb_rs_frobSq
  have hpt : ∀ i j : Fin 2, ‖(A + B) i j‖ ^ 2 ≤ 2 * ‖A i j‖ ^ 2 + 2 * ‖B i j‖ ^ 2 := by
    intro i j
    change ‖A i j + B i j‖ ^ 2 ≤ 2 * ‖A i j‖ ^ 2 + 2 * ‖B i j‖ ^ 2
    have htri : ‖A i j + B i j‖ ≤ ‖A i j‖ + ‖B i j‖ := norm_add_le _ _
    have hsq : ‖A i j + B i j‖ ^ 2 ≤ (‖A i j‖ + ‖B i j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖A i j‖ - ‖B i j‖)]
  calc ∑ i : Fin 2, ∑ j : Fin 2, ‖(A + B) i j‖ ^ 2
      ≤ ∑ i : Fin 2, ∑ j : Fin 2, (2 * ‖A i j‖ ^ 2 + 2 * ‖B i j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    _ = 2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖A i j‖ ^ 2) +
          2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖B i j‖ ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]

private lemma pb_rs_su2_row1 (Y : SU 2) :
    (Y : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -star ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1) ∧
    (Y : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = star ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  have hmem := Y.2
  rw [Matrix.mem_specialUnitaryGroup_iff] at hmem
  have hmul : (Y : Matrix (Fin 2) (Fin 2) ℂ) * star (Y : Matrix (Fin 2) (Fin 2) ℂ) = 1 := hmem.1.2
  have hdet : (Y : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := hmem.2
  have h00 : (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * star ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0) +
      (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * star ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = 1 := by
    have := congrFun (congrFun hmul 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] using this
  have h01 : (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * star ((Y : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
      (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * star ((Y : Matrix (Fin 2) (Fin 2) ℂ) 1 1) = 0 := by
    have := congrFun (congrFun hmul 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] using this
  have h01' : star ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * (Y : Matrix (Fin 2) (Fin 2) ℂ) 1 0 +
      star ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1) * (Y : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := by
    have hs := congrArg star h01
    simpa [mul_comm] using hs
  have hdet' : (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (Y : Matrix (Fin 2) (Fin 2) ℂ) 1 1 -
      (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (Y : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdet
  constructor
  · linear_combination
      -(Y : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * h00 +
      (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * h01' -
      star ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1) * hdet'
  · linear_combination
      -(Y : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * h00 +
      (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * h01' +
      star ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * hdet'

private lemma pb_rs_frobSq_su2_diff (Y Z : SU 2) :
    pb_rs_frobSq ((Y : Matrix (Fin 2) (Fin 2) ℂ) - (Z : Matrix (Fin 2) (Fin 2) ℂ)) =
      2 * (‖(Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0 - (Z : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ 2 +
           ‖(Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1 - (Z : Matrix (Fin 2) (Fin 2) ℂ) 0 1‖ ^ 2) := by
  have hy := pb_rs_su2_row1 Y
  have hz := pb_rs_su2_row1 Z
  have h10 : ‖(Y : Matrix (Fin 2) (Fin 2) ℂ) 1 0 - (Z : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ =
      ‖(Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1 - (Z : Matrix (Fin 2) (Fin 2) ℂ) 0 1‖ := by
    rw [hy.1, hz.1]
    have heq : -star ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1) -
        -star ((Z : Matrix (Fin 2) (Fin 2) ℂ) 0 1) =
        -star ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1 - (Z : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
      simp [sub_eq_add_neg, add_comm]
    rw [heq, norm_neg, norm_star]
  have h11 : ‖(Y : Matrix (Fin 2) (Fin 2) ℂ) 1 1 - (Z : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ =
      ‖(Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0 - (Z : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ := by
    rw [hy.2, hz.2, ← star_sub, norm_star]
  unfold pb_rs_frobSq
  simp only [Fin.sum_univ_two, Matrix.sub_apply, h10, h11]
  ring

/-! ### 2. Frobenius balls and Haar measure lower bound on SU(2) -/

private def pb_rs_ballF (X : SU 2) (r : ℝ) : Set (SU 2) :=
  {Y : SU 2 | pb_rs_frobSq ((Y : Matrix (Fin 2) (Fin 2) ℂ) - (X : Matrix (Fin 2) (Fin 2) ℂ)) < r ^ 2}

private lemma pb_rs_isOpen_ballF (X : SU 2) (r : ℝ) : IsOpen (pb_rs_ballF X r) := by
  have hsub : Continuous fun Y : SU 2 => (Y : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  have hcont : Continuous fun Y : SU 2 =>
      pb_rs_frobSq ((Y : Matrix (Fin 2) (Fin 2) ℂ) - (X : Matrix (Fin 2) (Fin 2) ℂ)) := by
    unfold pb_rs_frobSq
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((continuous_apply_apply i j).comp hsub).sub continuous_const).norm.pow 2
  exact isOpen_lt hcont continuous_const

private lemma pb_rs_measurableSet_ballF (X : SU 2) (r : ℝ) : MeasurableSet (pb_rs_ballF X r) :=
  (pb_rs_isOpen_ballF X r).measurableSet

private lemma pb_rs_preimage_mul_ballF (X : SU 2) (r : ℝ) :
    (fun Y : SU 2 => X * Y) ⁻¹' pb_rs_ballF X r = pb_rs_ballF 1 r := by
  ext Y
  simp only [Set.mem_preimage, pb_rs_ballF, Set.mem_ofPred_eq]
  have hsub : ((X * Y : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) - (X : Matrix (Fin 2) (Fin 2) ℂ) =
      (X : Matrix (Fin 2) (Fin 2) ℂ) * ((Y : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
    simp [mul_sub]
  rw [hsub, pb_rs_frobSq_mul_unitary_left (Matrix.specialUnitaryGroup_le_unitaryGroup X.2)]
  rfl

private lemma pb_rs_haar_ballF_eq (X : SU 2) (r : ℝ) :
    haarSU 2 (pb_rs_ballF X r) = haarSU 2 (pb_rs_ballF 1 r) := by
  calc haarSU 2 (pb_rs_ballF X r)
      = haarSU 2 ((fun Y : SU 2 => X * Y) ⁻¹' pb_rs_ballF X r) :=
        (MeasureTheory.measure_preimage_mul (haarSU 2) X (pb_rs_ballF X r)).symm
    _ = haarSU 2 (pb_rs_ballF 1 r) := by rw [pb_rs_preimage_mul_ballF]

private noncomputable def pb_rs_su2Coord (Y : SU 2) : Fin 4 → ℝ :=
  ![((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re,
    ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im,
    ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re,
    ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im]

private lemma pb_rs_su2Coord_bound (Y : SU 2) (i : Fin 4) :
    -1 ≤ pb_rs_su2Coord Y i ∧ pb_rs_su2Coord Y i ≤ 1 := by
  have h00 : ‖(Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ≤ 1 :=
    entry_norm_bound_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup Y.2) 0 0
  have h01 : ‖(Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1‖ ≤ 1 :=
    entry_norm_bound_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup Y.2) 0 1
  fin_cases i
  · exact abs_le.mp ((Complex.abs_re_le_norm _).trans h00)
  · exact abs_le.mp ((Complex.abs_im_le_norm _).trans h00)
  · exact abs_le.mp ((Complex.abs_re_le_norm _).trans h01)
  · exact abs_le.mp ((Complex.abs_im_le_norm _).trans h01)

private noncomputable def pb_rs_coordBucket (N : ℕ) (hN : 0 < N) (x : ℝ) : Fin N :=
  ⟨min (Nat.floor (((x + 1) / 2) * (N : ℝ))) (N - 1), by
    exact lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hN zero_lt_one)⟩

private lemma pb_rs_coordBucket_interval (N : ℕ) (hN : 0 < N) {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) :
    (((pb_rs_coordBucket N hN x : ℕ) : ℝ)) ≤ ((x + 1) / 2) * (N : ℝ) ∧
      ((x + 1) / 2) * (N : ℝ) ≤ (((pb_rs_coordBucket N hN x : ℕ) : ℝ)) + 1 := by
  set t : ℝ := ((x + 1) / 2) * (N : ℝ)
  have hhalf0 : 0 ≤ (x + 1) / 2 := by linarith [hx.1]
  have hhalf1 : (x + 1) / 2 ≤ 1 := by linarith [hx.2]
  have ht0 : 0 ≤ t := mul_nonneg hhalf0 (Nat.cast_nonneg N)
  have htN : t ≤ (N : ℝ) := mul_le_of_le_one_left (Nat.cast_nonneg N) hhalf1
  dsimp only [pb_rs_coordBucket]
  by_cases hfl : Nat.floor t ≤ N - 1
  · rw [min_eq_left hfl]
    exact ⟨Nat.floor_le ht0, (Nat.lt_floor_add_one t).le⟩
  · have hge : N ≤ Nat.floor t := by omega
    have hm : min (Nat.floor t) (N - 1) = N - 1 := min_eq_right (by omega)
    rw [hm]
    have hN1 : (1 : ℕ) ≤ N := hN
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub hN1, Nat.cast_one]
    have ht_ge : (N : ℝ) ≤ t := by
      calc (N : ℝ) = ((N : ℕ) : ℝ) := rfl
        _ ≤ ((Nat.floor t : ℕ) : ℝ) := by exact_mod_cast hge
        _ ≤ t := Nat.floor_le ht0
    rw [hcast]
    constructor <;> linarith

private lemma pb_rs_coordBucket_diff_le (N : ℕ) (hN : 0 < N) {x y : ℝ}
    (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1)
    (heq : pb_rs_coordBucket N hN x = pb_rs_coordBucket N hN y) :
    |x - y| ≤ 2 / (N : ℝ) := by
  have hx' := pb_rs_coordBucket_interval N hN hx
  have hy' := pb_rs_coordBucket_interval N hN hy
  rw [heq] at hx'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiff1 : ((x + 1) / 2) * (N : ℝ) - ((y + 1) / 2) * (N : ℝ) ≤ 1 := by linarith [hx'.2, hy'.1]
  have hdiff2 : ((y + 1) / 2) * (N : ℝ) - ((x + 1) / 2) * (N : ℝ) ≤ 1 := by linarith [hy'.2, hx'.1]
  have hmul1 : (x - y) * (N : ℝ) ≤ 2 := by linarith
  have hmul2 : (y - x) * (N : ℝ) ≤ 2 := by linarith
  rw [abs_le]
  constructor
  · have : y - x ≤ 2 / (N : ℝ) := (le_div_iff₀ hNpos).mpr hmul2
    linarith
  · exact (le_div_iff₀ hNpos).mpr hmul1

private lemma pb_rs_haar_ballF_lower {r : ℝ} (hr : 0 < r) :
    1 / ((Nat.ceil (8 / r) + 1 : ℕ) : ℝ) ^ 4 ≤ (haarSU 2 (pb_rs_ballF 1 r)).toReal := by
  classical
  let N : ℕ := Nat.ceil (8 / r) + 1
  have hN : 0 < N := Nat.succ_pos _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr : 8 / r < (N : ℝ) := by
    have h1 : 8 / r ≤ (Nat.ceil (8 / r) : ℝ) := Nat.le_ceil _
    have h2 : (N : ℝ) = (Nat.ceil (8 / r) : ℝ) + 1 := by push_cast [N]; rfl
    linarith
  have h2N : 2 / (N : ℝ) < r / 4 := by
    rw [div_lt_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 4)]
    have hmul : 8 < (N : ℝ) * r := (div_lt_iff₀ hr).mp hNr
    linarith
  let bucket : SU 2 → (Fin 4 → Fin N) := fun Y i => pb_rs_coordBucket N hN (pb_rs_su2Coord Y i)
  let activeBoxes : Finset (Fin 4 → Fin N) :=
    Finset.univ.filter (fun b => ∃ Z : SU 2, bucket Z = b)
  let rep : (b : Fin 4 → Fin N) → SU 2 :=
    fun b => if hb : ∃ Z : SU 2, bucket Z = b then Classical.choose hb else 1
  have hrep : ∀ (b : Fin 4 → Fin N), b ∈ activeBoxes → bucket (rep b) = b := by
    intro b hb
    have hEx : ∃ Z : SU 2, bucket Z = b := (Finset.mem_filter.mp hb).2
    dsimp only [rep]
    rw [dif_pos hEx]
    exact Classical.choose_spec hEx
  have hcover : (Set.univ : Set (SU 2)) ⊆ ⋃ b ∈ activeBoxes, pb_rs_ballF (rep b) r := by
    intro Y _
    have hb_mem : bucket Y ∈ activeBoxes := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨Y, rfl⟩⟩
    refine Set.mem_iUnion.mpr ⟨bucket Y, Set.mem_iUnion.mpr ⟨hb_mem, ?_⟩⟩
    set Z := rep (bucket Y)
    have hYZ : bucket Y = bucket Z := (hrep (bucket Y) hb_mem).symm
    have hcoord : ∀ i : Fin 4, (pb_rs_su2Coord Y i - pb_rs_su2Coord Z i) ^ 2 < (r / 4) ^ 2 := by
      intro i
      have hdiff : |pb_rs_su2Coord Y i - pb_rs_su2Coord Z i| ≤ 2 / (N : ℝ) :=
        pb_rs_coordBucket_diff_le N hN (pb_rs_su2Coord_bound Y i) (pb_rs_su2Coord_bound Z i)
          (congrFun hYZ i)
      have habs : |pb_rs_su2Coord Y i - pb_rs_su2Coord Z i| < r / 4 := hdiff.trans_lt h2N
      rw [← sq_abs (pb_rs_su2Coord Y i - pb_rs_su2Coord Z i)]
      exact sq_lt_sq' (by linarith [abs_nonneg (pb_rs_su2Coord Y i - pb_rs_su2Coord Z i)]) habs
    change pb_rs_frobSq ((Y : Matrix (Fin 2) (Fin 2) ℂ) - (Z : Matrix (Fin 2) (Fin 2) ℂ)) < r ^ 2
    rw [pb_rs_frobSq_su2_diff]
    have hre00 : ‖(Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0 - (Z : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ 2 =
        (pb_rs_su2Coord Y 0 - pb_rs_su2Coord Z 0) ^ 2 +
        (pb_rs_su2Coord Y 1 - pb_rs_su2Coord Z 1) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [pb_rs_su2Coord]
      ring
    have hre01 : ‖(Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1 - (Z : Matrix (Fin 2) (Fin 2) ℂ) 0 1‖ ^ 2 =
        (pb_rs_su2Coord Y 2 - pb_rs_su2Coord Z 2) ^ 2 +
        (pb_rs_su2Coord Y 3 - pb_rs_su2Coord Z 3) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [pb_rs_su2Coord]
      ring
    rw [hre00, hre01]
    have h0 := hcoord 0
    have h1 := hcoord 1
    have h2 := hcoord 2
    have h3 := hcoord 3
    nlinarith
  have hm_le : (1 : ENNReal) ≤ (activeBoxes.card : ENNReal) * haarSU 2 (pb_rs_ballF 1 r) := by
    calc (1 : ENNReal)
        = haarSU 2 Set.univ := measure_univ.symm
      _ ≤ haarSU 2 (⋃ b ∈ activeBoxes, pb_rs_ballF (rep b) r) := measure_mono hcover
      _ ≤ ∑ b ∈ activeBoxes, haarSU 2 (pb_rs_ballF (rep b) r) := measure_biUnion_finset_le _ _
      _ = ∑ _b ∈ activeBoxes, haarSU 2 (pb_rs_ballF 1 r) :=
          Finset.sum_congr rfl fun b _ => pb_rs_haar_ballF_eq (rep b) r
      _ = (activeBoxes.card : ENNReal) * haarSU 2 (pb_rs_ballF 1 r) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : activeBoxes.card ≤ N ^ 4 := by
    calc activeBoxes.card
        ≤ (Finset.univ : Finset (Fin 4 → Fin N)).card := Finset.card_filter_le _ _
      _ = N ^ 4 := by simp [Fintype.card_fin]
  have hm_le2 : (1 : ENNReal) ≤ ((N ^ 4 : ℕ) : ENNReal) * haarSU 2 (pb_rs_ballF 1 r) := by
    refine hm_le.trans ?_
    gcongr
  have hreal : (1 : ℝ) ≤ (N : ℝ) ^ 4 * (haarSU 2 (pb_rs_ballF 1 r)).toReal := by
    have hne_top1 : ((N ^ 4 : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hne_top2 : haarSU 2 (pb_rs_ballF 1 r) ≠ ⊤ := measure_ne_top _ _
    have hto := ENNReal.toReal_mono (ENNReal.mul_ne_top hne_top1 hne_top2) hm_le2
    rw [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hto
    push_cast at hto
    exact hto
  rw [div_le_iff₀ (pow_pos hNpos 4)]
  linarith

/-! ### 3. Lazy walk operator contraction on L²₀(SU 2, haarSU 2) -/

private noncomputable def pb_rs_lazyM (g : Fin 2 → SU 2) (f : SU 2 → ℂ) : SU 2 → ℂ :=
  fun x => (1 / 4 : ℂ) * heckeOperator g f x

private noncomputable def pb_rs_lazyP (g : Fin 2 → SU 2) (f : SU 2 → ℂ) : SU 2 → ℂ :=
  fun x => (1 / 2 : ℂ) * f x + (1 / 2 : ℂ) * pb_rs_lazyM g f x

private lemma pb_rs_hecke_memLp (g : Fin 2 → SU 2) {f : SU 2 → ℂ}
    (hf : MemLp f 2 (haarSU 2)) :
    MemLp (heckeOperator g f) 2 (haarSU 2) := by
  have hshift : ∀ s : SU 2, MemLp (fun x => f (s * x)) 2 (haarSU 2) := fun s =>
    hf.comp_measurePreserving (measurePreserving_mul_left (haarSU 2) s)
  have hterm : ∀ j : Fin 2, MemLp (fun x => f (g j * x) + f ((g j)⁻¹ * x)) 2 (haarSU 2) :=
    fun j => (hshift (g j)).add (hshift (g j)⁻¹)
  have heq : heckeOperator g f =
      fun x => (f (g 0 * x) + f ((g 0)⁻¹ * x)) + (f (g 1 * x) + f ((g 1)⁻¹ * x)) := by
    funext x
    simp [heckeOperator, Fin.sum_univ_two]
  rw [heq]
  exact (hterm 0).add (hterm 1)

private lemma pb_rs_lazyM_memLp (g : Fin 2 → SU 2) {f : SU 2 → ℂ}
    (hf : MemLp f 2 (haarSU 2)) :
    MemLp (pb_rs_lazyM g f) 2 (haarSU 2) :=
  (pb_rs_hecke_memLp g hf).const_smul (1 / 4 : ℂ)

private lemma pb_rs_lazyP_memLp (g : Fin 2 → SU 2) {f : SU 2 → ℂ}
    (hf : MemLp f 2 (haarSU 2)) :
    MemLp (pb_rs_lazyP g f) 2 (haarSU 2) :=
  (hf.const_smul (1 / 2 : ℂ)).add ((pb_rs_lazyM_memLp g hf).const_smul (1 / 2 : ℂ))

private lemma pb_rs_integral_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : SU 2 → E} (hf : Integrable f (haarSU 2)) (hg : Integrable g (haarSU 2)) :
    ∫ x, f x + g x ∂(haarSU 2) = ∫ x, f x ∂(haarSU 2) + ∫ x, g x ∂(haarSU 2) :=
  integral_add hf hg

private lemma pb_rs_lazyP_integral_zero (g : Fin 2 → SU 2) {f : SU 2 → ℂ}
    (hf : MemLp f 2 (haarSU 2)) (hf0 : ∫ x, f x ∂(haarSU 2) = 0) :
    ∫ x, pb_rs_lazyP g f x ∂(haarSU 2) = 0 := by
  have hint_f : Integrable f (haarSU 2) := hf.integrable one_le_two
  have hint_shift : ∀ s : SU 2, Integrable (fun x => f (s * x)) (haarSU 2) := fun s =>
    (hf.comp_measurePreserving (measurePreserving_mul_left (haarSU 2) s)).integrable one_le_two
  have hint_shift0 : ∀ s : SU 2, ∫ x, f (s * x) ∂(haarSU 2) = 0 := fun s => by
    rw [integral_mul_left_eq_self, hf0]
  have hhecke0 : ∫ x, heckeOperator g f x ∂(haarSU 2) = 0 := by
    have heq : heckeOperator g f =
        fun x => (f (g 0 * x) + f ((g 0)⁻¹ * x)) + (f (g 1 * x) + f ((g 1)⁻¹ * x)) := by
      funext x
      simp [heckeOperator, Fin.sum_univ_two]
    rw [heq]
    have h01 : Integrable (fun x => f (g 0 * x) + f ((g 0)⁻¹ * x)) (haarSU 2) :=
      (hint_shift (g 0)).add (hint_shift (g 0)⁻¹)
    have h23 : Integrable (fun x => f (g 1 * x) + f ((g 1)⁻¹ * x)) (haarSU 2) :=
      (hint_shift (g 1)).add (hint_shift (g 1)⁻¹)
    dsimp only
    rw [pb_rs_integral_add h01 h23,
      pb_rs_integral_add (hint_shift (g 0)) (hint_shift (g 0)⁻¹),
      pb_rs_integral_add (hint_shift (g 1)) (hint_shift (g 1)⁻¹),
      hint_shift0, hint_shift0, hint_shift0, hint_shift0]
    norm_num
  have hint_M : Integrable (pb_rs_lazyM g f) (haarSU 2) :=
    (pb_rs_lazyM_memLp g hf).integrable one_le_two
  have hM0 : ∫ x, pb_rs_lazyM g f x ∂(haarSU 2) = 0 := by
    change ∫ x, (1 / 4 : ℂ) • heckeOperator g f x ∂(haarSU 2) = 0
    rw [integral_smul, hhecke0, smul_zero]
  have h1 : Integrable (fun x => (1 / 2 : ℂ) • f x) (haarSU 2) := hint_f.smul (1 / 2 : ℂ)
  have h2 : Integrable (fun x => (1 / 2 : ℂ) • pb_rs_lazyM g f x) (haarSU 2) :=
    hint_M.smul (1 / 2 : ℂ)
  change ∫ x, (1 / 2 : ℂ) • f x + (1 / 2 : ℂ) • pb_rs_lazyM g f x ∂(haarSU 2) = 0
  rw [pb_rs_integral_add h1 h2, integral_smul, integral_smul, hf0, hM0]
  simp

private lemma pb_rs_lazyM_l2_contraction (g : Fin 2 → SU 2) {f : SU 2 → ℂ}
    (hf : MemLp f 2 (haarSU 2)) :
    ∫ x, ‖pb_rs_lazyM g f x‖ ^ 2 ∂(haarSU 2) ≤ ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2) := by
  have hshift_sq : ∀ s : SU 2, Integrable (fun x => ‖f (s * x)‖ ^ 2) (haarSU 2) := fun s =>
    ((hf.comp_measurePreserving (measurePreserving_mul_left (haarSU 2) s)).norm).integrable_sq
  have hM_sq : Integrable (fun x => ‖pb_rs_lazyM g f x‖ ^ 2) (haarSU 2) :=
    (pb_rs_lazyM_memLp g hf).norm.integrable_sq
  have hpt : ∀ x : SU 2, ‖pb_rs_lazyM g f x‖ ^ 2 ≤
      (1 / 4 : ℝ) * (‖f (g 0 * x)‖ ^ 2 + ‖f ((g 0)⁻¹ * x)‖ ^ 2 +
        ‖f (g 1 * x)‖ ^ 2 + ‖f ((g 1)⁻¹ * x)‖ ^ 2) := by
    intro x
    set a := ‖f (g 0 * x)‖
    set b := ‖f ((g 0)⁻¹ * x)‖
    set c := ‖f (g 1 * x)‖
    set d := ‖f ((g 1)⁻¹ * x)‖
    have hnorm : ‖pb_rs_lazyM g f x‖ ≤ (1 / 4 : ℝ) * (a + b + c + d) := by
      have hm : pb_rs_lazyM g f x = (1 / 4 : ℂ) *
          ((f (g 0 * x) + f ((g 0)⁻¹ * x)) + (f (g 1 * x) + f ((g 1)⁻¹ * x))) := by
        simp [pb_rs_lazyM, heckeOperator, Fin.sum_univ_two]
      rw [hm, norm_mul]
      have h14 : ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) := by norm_num
      rw [h14]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc ‖(f (g 0 * x) + f ((g 0)⁻¹ * x)) + (f (g 1 * x) + f ((g 1)⁻¹ * x))‖
          ≤ ‖f (g 0 * x) + f ((g 0)⁻¹ * x)‖ + ‖f (g 1 * x) + f ((g 1)⁻¹ * x)‖ := norm_add_le _ _
        _ ≤ (a + b) + (c + d) := add_le_add (norm_add_le _ _) (norm_add_le _ _)
        _ = a + b + c + d := by ring
    have hsq : ‖pb_rs_lazyM g f x‖ ^ 2 ≤ ((1 / 4 : ℝ) * (a + b + c + d)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
      sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  have h01 : Integrable (fun x => ‖f (g 0 * x)‖ ^ 2 + ‖f ((g 0)⁻¹ * x)‖ ^ 2) (haarSU 2) :=
    (hshift_sq (g 0)).add (hshift_sq (g 0)⁻¹)
  have h012 : Integrable (fun x => ‖f (g 0 * x)‖ ^ 2 + ‖f ((g 0)⁻¹ * x)‖ ^ 2 +
      ‖f (g 1 * x)‖ ^ 2) (haarSU 2) := h01.add (hshift_sq (g 1))
  have hrhs_int : Integrable (fun x => (1 / 4 : ℝ) * (‖f (g 0 * x)‖ ^ 2 + ‖f ((g 0)⁻¹ * x)‖ ^ 2 +
      ‖f (g 1 * x)‖ ^ 2 + ‖f ((g 1)⁻¹ * x)‖ ^ 2)) (haarSU 2) :=
    (h012.add (hshift_sq (g 1)⁻¹)).const_mul _
  have hint_le := integral_mono hM_sq hrhs_int hpt
  have hrhs_eq : (∫ x, (1 / 4 : ℝ) * (‖f (g 0 * x)‖ ^ 2 + ‖f ((g 0)⁻¹ * x)‖ ^ 2 +
      ‖f (g 1 * x)‖ ^ 2 + ‖f ((g 1)⁻¹ * x)‖ ^ 2) ∂(haarSU 2)) =
      ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2) := by
    rw [integral_const_mul,
      pb_rs_integral_add h012 (hshift_sq (g 1)⁻¹),
      pb_rs_integral_add h01 (hshift_sq (g 1)),
      pb_rs_integral_add (hshift_sq (g 0)) (hshift_sq (g 0)⁻¹),
      integral_mul_left_eq_self (fun x => ‖f x‖ ^ 2) (g 0),
      integral_mul_left_eq_self (fun x => ‖f x‖ ^ 2) (g 0)⁻¹,
      integral_mul_left_eq_self (fun x => ‖f x‖ ^ 2) (g 1),
      integral_mul_left_eq_self (fun x => ‖f x‖ ^ 2) (g 1)⁻¹]
    ring
  linarith

private lemma pb_rs_half_sum_sq (u v : ℂ) :
    ‖(1 / 2 : ℂ) * u + (1 / 2 : ℂ) * v‖ ^ 2 =
      (1 / 4 : ℝ) * ‖u‖ ^ 2 + (1 / 4 : ℝ) * ‖v‖ ^ 2 +
        (1 / 2 : ℝ) * (starRingEnd ℂ u * v).re := by
  have heq : (1 / 2 : ℂ) * u + (1 / 2 : ℂ) * v = (1 / 2 : ℂ) * (u + v) := by ring
  rw [heq, norm_mul, mul_pow]
  have h12 : ‖(1 / 2 : ℂ)‖ ^ 2 = (1 / 4 : ℝ) := by norm_num
  rw [h12, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

private lemma pb_rs_lazyP_step_bound (g : Fin 2 → SU 2) {ε_gap : ℝ}
    (hgap : ∀ f : SU 2 → ℂ, MemLp f 2 (haarSU 2) → ∫ x, f x ∂(haarSU 2) = 0 →
      (∫ x, starRingEnd ℂ (f x) * heckeOperator g f x ∂(haarSU 2)).re ≤
        (2 * (2 : ℕ) - ε_gap) * ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2))
    {f : SU 2 → ℂ} (hf : MemLp f 2 (haarSU 2)) (hf0 : ∫ x, f x ∂(haarSU 2) = 0) :
    ∫ x, ‖pb_rs_lazyP g f x‖ ^ 2 ∂(haarSU 2) ≤
      max (1 / 2 : ℝ) (1 - ε_gap / 8) * ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2) := by
  have hm : MemLp (pb_rs_lazyM g f) 2 (haarSU 2) := pb_rs_lazyM_memLp g hf
  have hfconj : MemLp (fun x => starRingEnd ℂ (f x)) 2 (haarSU 2) :=
    Complex.conjCLE.toContinuousLinearMap.comp_memLp' hf
  have hint_f2 : Integrable (fun x => ‖f x‖ ^ 2) (haarSU 2) := hf.norm.integrable_sq
  have hint_M2 : Integrable (fun x => ‖pb_rs_lazyM g f x‖ ^ 2) (haarSU 2) := hm.norm.integrable_sq
  have hint_prod : Integrable (fun x => starRingEnd ℂ (f x) * pb_rs_lazyM g f x) (haarSU 2) :=
    hfconj.integrable_mul hm
  have hint_re : Integrable (fun x => (starRingEnd ℂ (f x) * pb_rs_lazyM g f x).re) (haarSU 2) :=
    hint_prod.re
  have hpt : (fun x => ‖pb_rs_lazyP g f x‖ ^ 2) = fun x =>
      (1 / 4 : ℝ) * ‖f x‖ ^ 2 + (1 / 4 : ℝ) * ‖pb_rs_lazyM g f x‖ ^ 2 +
        (1 / 2 : ℝ) * (starRingEnd ℂ (f x) * pb_rs_lazyM g f x).re := by
    funext x
    exact pb_rs_half_sum_sq (f x) (pb_rs_lazyM g f x)
  have hf2_mul : Integrable (fun x => (1 / 4 : ℝ) * ‖f x‖ ^ 2) (haarSU 2) :=
    hint_f2.const_mul (1 / 4 : ℝ)
  have hM2_mul : Integrable (fun x => (1 / 4 : ℝ) * ‖pb_rs_lazyM g f x‖ ^ 2) (haarSU 2) :=
    hint_M2.const_mul (1 / 4 : ℝ)
  have hsum12 : Integrable (fun x => (1 / 4 : ℝ) * ‖f x‖ ^ 2 +
      (1 / 4 : ℝ) * ‖pb_rs_lazyM g f x‖ ^ 2) (haarSU 2) := hf2_mul.add hM2_mul
  have hre_mul : Integrable (fun x => (1 / 2 : ℝ) *
      (starRingEnd ℂ (f x) * pb_rs_lazyM g f x).re) (haarSU 2) :=
    hint_re.const_mul (1 / 2 : ℝ)
  have hsplit : ∫ x, ‖pb_rs_lazyP g f x‖ ^ 2 ∂(haarSU 2) =
      (1 / 4 : ℝ) * ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2) +
      (1 / 4 : ℝ) * ∫ x, ‖pb_rs_lazyM g f x‖ ^ 2 ∂(haarSU 2) +
      (1 / 2 : ℝ) * ∫ x, (starRingEnd ℂ (f x) * pb_rs_lazyM g f x).re ∂(haarSU 2) := by
    rw [hpt]
    rw [pb_rs_integral_add hsum12 hre_mul, pb_rs_integral_add hf2_mul hM2_mul,
      integral_const_mul, integral_const_mul, integral_const_mul]
  have hre_eq : ∫ x, (starRingEnd ℂ (f x) * pb_rs_lazyM g f x).re ∂(haarSU 2) =
      (1 / 4 : ℝ) * (∫ x, starRingEnd ℂ (f x) * heckeOperator g f x ∂(haarSU 2)).re := by
    change ∫ x, RCLike.re (starRingEnd ℂ (f x) * pb_rs_lazyM g f x) ∂(haarSU 2) = _
    rw [integral_re hint_prod]
    have hsmul : (fun x => starRingEnd ℂ (f x) * pb_rs_lazyM g f x) =
        fun x => (1 / 4 : ℝ) • (starRingEnd ℂ (f x) * heckeOperator g f x) := by
      funext x
      simp [pb_rs_lazyM, Complex.real_smul]
      ring
    rw [hsmul, integral_smul]
    simp
  have hM_le := pb_rs_lazyM_l2_contraction g hf
  have hgap_f := hgap f hf hf0
  norm_num at hgap_f
  have hI_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2) := integral_nonneg fun _ => sq_nonneg _
  have hq_ge : 1 - ε_gap / 8 ≤ max (1 / 2 : ℝ) (1 - ε_gap / 8) := le_max_right _ _
  calc ∫ x, ‖pb_rs_lazyP g f x‖ ^ 2 ∂(haarSU 2)
      = (1 / 4 : ℝ) * ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2) +
        (1 / 4 : ℝ) * ∫ x, ‖pb_rs_lazyM g f x‖ ^ 2 ∂(haarSU 2) +
        (1 / 2 : ℝ) * ((1 / 4 : ℝ) *
          (∫ x, starRingEnd ℂ (f x) * heckeOperator g f x ∂(haarSU 2)).re) := by
          rw [hsplit, hre_eq]
    _ ≤ (1 / 4 : ℝ) * ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2) +
        (1 / 4 : ℝ) * ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2) +
        (1 / 8 : ℝ) * ((4 - ε_gap) * ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2)) := by linarith
    _ = (1 - ε_gap / 8) * ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2) := by ring
    _ ≤ max (1 / 2 : ℝ) (1 - ε_gap / 8) * ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2) :=
        mul_le_mul_of_nonneg_right hq_ge hI_nonneg

private lemma pb_rs_lazyP_iter_bound (g : Fin 2 → SU 2) {ε_gap : ℝ}
    (hgap : ∀ f : SU 2 → ℂ, MemLp f 2 (haarSU 2) → ∫ x, f x ∂(haarSU 2) = 0 →
      (∫ x, starRingEnd ℂ (f x) * heckeOperator g f x ∂(haarSU 2)).re ≤
        (2 * (2 : ℕ) - ε_gap) * ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2))
    {f : SU 2 → ℂ} (hf : MemLp f 2 (haarSU 2)) (hf0 : ∫ x, f x ∂(haarSU 2) = 0) :
    ∀ ℓ : ℕ, MemLp ((pb_rs_lazyP g)^[ℓ] f) 2 (haarSU 2) ∧
      (∫ x, ((pb_rs_lazyP g)^[ℓ] f) x ∂(haarSU 2) = 0) ∧
      ∫ x, ‖((pb_rs_lazyP g)^[ℓ] f) x‖ ^ 2 ∂(haarSU 2) ≤
        (max (1 / 2 : ℝ) (1 - ε_gap / 8)) ^ ℓ * ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2) := by
  intro ℓ
  induction ℓ with
  | zero =>
    exact ⟨hf, hf0, by simp⟩
  | succ ℓ ih =>
    rcases ih with ⟨hmem, hint0, hbound⟩
    have hq_nonneg : 0 ≤ max (1 / 2 : ℝ) (1 - ε_gap / 8) :=
      le_trans (by norm_num) (le_max_left _ _)
    refine ⟨?_, ?_, ?_⟩
    · simpa [Function.iterate_succ_apply'] using pb_rs_lazyP_memLp g hmem
    · simpa [Function.iterate_succ_apply'] using pb_rs_lazyP_integral_zero g hmem hint0
    · rw [Function.iterate_succ_apply', pow_succ']
      calc ∫ x, ‖pb_rs_lazyP g ((pb_rs_lazyP g)^[ℓ] f) x‖ ^ 2 ∂(haarSU 2)
          ≤ max (1 / 2 : ℝ) (1 - ε_gap / 8) *
              ∫ x, ‖((pb_rs_lazyP g)^[ℓ] f) x‖ ^ 2 ∂(haarSU 2) :=
            pb_rs_lazyP_step_bound g hgap hmem hint0
        _ ≤ max (1 / 2 : ℝ) (1 - ε_gap / 8) *
              ((max (1 / 2 : ℝ) (1 - ε_gap / 8)) ^ ℓ * ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2)) :=
            mul_le_mul_of_nonneg_left hbound hq_nonneg
        _ = (max (1 / 2 : ℝ) (1 - ε_gap / 8) * (max (1 / 2 : ℝ) (1 - ε_gap / 8)) ^ ℓ) *
              ∫ x, ‖f x‖ ^ 2 ∂(haarSU 2) := by ring

/-! ### 4. Word extraction and SU(2) approximation -/

private def pb_rs_genStep (g : Fin 2 → SU 2) (p : Bool × Fin 2) : SU 2 :=
  if p.1 then g p.2 else (g p.2)⁻¹

private def pb_rs_evalWord (g : Fin 2 → SU 2) (w : List (Bool × Fin 2)) : SU 2 :=
  (w.map (pb_rs_genStep g)).prod

private lemma pb_rs_evalWord_snoc (g : Fin 2 → SU 2) (w : List (Bool × Fin 2)) (p : Bool × Fin 2) :
    pb_rs_evalWord g (w ++ [p]) = pb_rs_evalWord g w * pb_rs_genStep g p := by
  simp [pb_rs_evalWord]

private lemma pb_rs_lazyP_sub_const (g : Fin 2 → SU 2) (h : SU 2 → ℂ) (c : ℂ) :
    ∀ ℓ : ℕ, ∀ x : SU 2,
      ((pb_rs_lazyP g)^[ℓ] (fun y => h y - c)) x = ((pb_rs_lazyP g)^[ℓ] h) x - c := by
  intro ℓ
  induction ℓ with
  | zero => intro x; rfl
  | succ ℓ ih =>
    intro x
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hfun : (pb_rs_lazyP g)^[ℓ] (fun y => h y - c) = fun y => ((pb_rs_lazyP g)^[ℓ] h) y - c :=
      funext ih
    rw [hfun]
    simp [pb_rs_lazyP, pb_rs_lazyM, heckeOperator, Fin.sum_univ_two]
    ring

private lemma pb_rs_lazyP_support_word (g : Fin 2 → SU 2) (B : Set (SU 2)) :
    ∀ ℓ : ℕ, ∀ x : SU 2,
      ((pb_rs_lazyP g)^[ℓ] (B.indicator fun _ => (1 : ℂ))) x ≠ 0 →
      ∃ w : List (Bool × Fin 2), w.length ≤ ℓ ∧ pb_rs_evalWord g w * x ∈ B := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro x hx
    simp only [Function.iterate_zero, id_eq] at hx
    refine ⟨[], le_rfl, ?_⟩
    simpa [pb_rs_evalWord] using Set.mem_of_indicator_ne_zero hx
  | succ ℓ ih =>
    intro x hx
    rw [Function.iterate_succ_apply'] at hx
    set F := (pb_rs_lazyP g)^[ℓ] (B.indicator fun _ => (1 : ℂ))
    by_cases h0 : F x ≠ 0
    · obtain ⟨w, hlen, hw⟩ := ih x h0
      exact ⟨w, by omega, hw⟩
    · by_cases h1 : F (g 0 * x) ≠ 0
      · obtain ⟨w, hlen, hw⟩ := ih (g 0 * x) h1
        refine ⟨w ++ [(true, 0)], by simp; omega, ?_⟩
        rw [pb_rs_evalWord_snoc, mul_assoc]
        exact hw
      · by_cases h2 : F ((g 0)⁻¹ * x) ≠ 0
        · obtain ⟨w, hlen, hw⟩ := ih ((g 0)⁻¹ * x) h2
          refine ⟨w ++ [(false, 0)], by simp; omega, ?_⟩
          rw [pb_rs_evalWord_snoc, mul_assoc]
          exact hw
        · by_cases h3 : F (g 1 * x) ≠ 0
          · obtain ⟨w, hlen, hw⟩ := ih (g 1 * x) h3
            refine ⟨w ++ [(true, 1)], by simp; omega, ?_⟩
            rw [pb_rs_evalWord_snoc, mul_assoc]
            exact hw
          · by_cases h4 : F ((g 1)⁻¹ * x) ≠ 0
            · obtain ⟨w, hlen, hw⟩ := ih ((g 1)⁻¹ * x) h4
              refine ⟨w ++ [(false, 1)], by simp; omega, ?_⟩
              rw [pb_rs_evalWord_snoc, mul_assoc]
              exact hw
            · exfalso
              push Not at h0 h1 h2 h3 h4
              apply hx
              simp [pb_rs_lazyP, pb_rs_lazyM, heckeOperator, Fin.sum_univ_two, h0, h1, h2, h3, h4]

private lemma pb_rs_su2_approx_of_gap (g : Fin 2 → SU 2)
    (hgap : HasSpectralGap (haarSU 2) g) :
    ∃ C_su2 : ℝ, 0 < C_su2 ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      ∀ V : SU 2, ∃ w : List (Bool × Fin 2),
        (w.length : ℝ) ≤ C_su2 * Real.log (1 / δ) ∧
        specNorm ((pb_rs_evalWord g w : Matrix (Fin 2) (Fin 2) ℂ) -
          (V : Matrix (Fin 2) (Fin 2) ℂ)) ≤ δ := by
  obtain ⟨ε_gap, hε_gap, hgap_spec⟩ := hgap
  let q : ℝ := max (1 / 2 : ℝ) (1 - ε_gap / 8)
  have hq_ge : 1 / 2 ≤ q := le_max_left _ _
  have hq_pos : 0 < q := by linarith
  have hq_lt1 : q < 1 := max_lt (by norm_num) (by linarith)
  have hlogq_neg : Real.log q < 0 := Real.log_neg hq_pos hq_lt1
  have hlog1q_pos : 0 < Real.log (1 / q) := by
    rw [one_div, Real.log_inv]
    linarith
  let A_c : ℝ := 8 / Real.log (1 / q)
  have hAc_pos : 0 < A_c := div_pos (by norm_num) hlog1q_pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C_su2 : ℝ := A_c * (Real.log 35 / Real.log 2 + 1) + 2 / Real.log 2
  have hC_pos : 0 < C_su2 := by positivity
  refine ⟨C_su2, hC_pos, fun δ hδ0 hδ12 V => ?_⟩
  let r : ℝ := δ / 2
  have hr : 0 < r := by positivity
  let B : Set (SU 2) := pb_rs_ballF 1 r
  have hB_meas : MeasurableSet B := pb_rs_measurableSet_ballF 1 r
  let m : ℝ := (haarSU 2 B).toReal
  have hm_lower : 1 / ((Nat.ceil (8 / r) + 1 : ℕ) : ℝ) ^ 4 ≤ m := pb_rs_haar_ballF_lower hr
  let N : ℕ := Nat.ceil (8 / r) + 1
  have hN_le : (N : ℝ) ≤ 35 / (2 * δ) := by
    have h8r : 8 / r = 16 / δ := by simp [r]; ring
    have h1 : (Nat.ceil (8 / r) : ℝ) < 8 / r + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (2 : ℝ) ≤ 1 / δ := by
      rw [le_div_iff₀ hδ0]
      linarith
    have h3 : (N : ℝ) < 16 / δ + 2 := by
      have : (N : ℝ) = (Nat.ceil (8 / r) : ℝ) + 1 := by push_cast [N]; rfl
      linarith
    have h4 : 16 / δ + 2 ≤ 35 / (2 * δ) := by
      have : 2 ≤ 3 / (2 * δ) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      linarith [show 16 / δ + 3 / (2 * δ) = 35 / (2 * δ) by ring]
    linarith
  have hN_pos : 0 < (N : ℝ) := by positivity
  have hm_delta : (2 * δ / 35) ^ 4 ≤ m := by
    have h1 : (2 * δ / 35) ^ 4 ≤ 1 / (N : ℝ) ^ 4 := by
      rw [one_div, ← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ 4
      have hmul : (N : ℝ) * (2 * δ) ≤ 35 := (le_div_iff₀ (by positivity)).mp hN_le
      have hdiv : (N : ℝ) * (2 * δ / 35) ≤ 1 := by
        rw [mul_div_assoc', div_le_one (by norm_num)]
        exact hmul
      rw [inv_eq_one_div, le_div_iff₀ hN_pos]
      linarith
    exact h1.trans hm_lower
  have hm_pos : 0 < m := lt_of_lt_of_le (by positivity) hm_delta
  have hm_le1 : m ≤ 1 := by
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  let ℓ : ℕ := Nat.ceil (8 * Real.log (35 / (2 * δ)) / Real.log (1 / q)) + 1
  have hℓ_gt : 8 * Real.log (35 / (2 * δ)) / Real.log (1 / q) < (ℓ : ℝ) := by
    have hle : 8 * Real.log (35 / (2 * δ)) / Real.log (1 / q) ≤
        (Nat.ceil (8 * Real.log (35 / (2 * δ)) / Real.log (1 / q)) : ℝ) := Nat.le_ceil _
    have hℓ_eq : (ℓ : ℝ) = (Nat.ceil (8 * Real.log (35 / (2 * δ)) / Real.log (1 / q)) : ℝ) + 1 := by
      push_cast [ℓ]; rfl
    linarith
  have hqℓ_lt_m2 : q ^ ℓ < m ^ 2 := by
    have hmul : 8 * Real.log (35 / (2 * δ)) < (ℓ : ℝ) * Real.log (1 / q) :=
      (div_lt_iff₀ hlog1q_pos).mp hℓ_gt
    have hlog_lt : (ℓ : ℝ) * Real.log q < 8 * Real.log (2 * δ / 35) := by
      have h1 : Real.log (1 / q) = -Real.log q := by rw [one_div, Real.log_inv]
      have h2 : Real.log (2 * δ / 35) = -Real.log (35 / (2 * δ)) := by
        rw [← Real.log_inv]; congr 1; field_simp
      rw [h1] at hmul
      rw [h2]
      linarith
    have hpow : q ^ ℓ < (2 * δ / 35) ^ 8 := by
      rw [← Real.rpow_natCast q ℓ, Real.rpow_def_of_pos hq_pos, mul_comm (Real.log q)]
      rw [← Real.rpow_natCast (2 * δ / 35) 8, Real.rpow_def_of_pos (by positivity),
        mul_comm (Real.log (2 * δ / 35))]
      exact Real.exp_lt_exp.mpr (by simpa using hlog_lt)
    have hm2_ge : (2 * δ / 35) ^ 8 ≤ m ^ 2 := by
      calc (2 * δ / 35) ^ 8 = ((2 * δ / 35) ^ 4) ^ 2 := by ring
        _ ≤ m ^ 2 := pow_le_pow_left₀ (by positivity) hm_delta 2
    exact hpow.trans_le hm2_ge
  let h₀ : SU 2 → ℂ := B.indicator (fun _ => (1 : ℂ))
  let f₀ : SU 2 → ℂ := fun x => h₀ x - (m : ℂ)
  have hf₀_meas : AEStronglyMeasurable f₀ (haarSU 2) := by
    have hh₀ : Measurable h₀ := measurable_const.indicator hB_meas
    exact (hh₀.sub measurable_const).aestronglyMeasurable
  have hf₀_mem : MemLp f₀ 2 (haarSU 2) := by
    refine MemLp.of_bound hf₀_meas (1 + m) (ae_of_all _ fun x => ?_)
    have hh_le : ‖h₀ x‖ ≤ 1 := by
      by_cases hx : x ∈ B <;> simp [h₀, hx]
    calc ‖h₀ x - (m : ℂ)‖ ≤ ‖h₀ x‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + m := by
          gcongr
          simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm_pos.le]
  have hh₀_int : Integrable h₀ (haarSU 2) :=
    (integrable_const (1 : ℂ)).indicator hB_meas
  have hf₀_int0 : ∫ x, f₀ x ∂(haarSU 2) = 0 := by
    rw [show f₀ = fun x => h₀ x - (m : ℂ) from rfl, integral_sub hh₀_int (integrable_const _)]
    have hh_val : ∫ x, h₀ x ∂(haarSU 2) = (m : ℂ) := by
      simp only [h₀]
      rw [integral_indicator hB_meas, setIntegral_const, MeasureTheory.measureReal_def]
      simp [m, Complex.real_smul]
    have hc_val : ∫ _x : SU 2, (m : ℂ) ∂(haarSU 2) = (m : ℂ) := by
      simp [integral_const]
    rw [hh_val, hc_val, sub_self]
  have hf₀_l2 : ∫ x, ‖f₀ x‖ ^ 2 ∂(haarSU 2) ≤ m := by
    have hpt : (fun x => ‖f₀ x‖ ^ 2) =
        fun x => (1 - 2 * m) * B.indicator (fun _ => (1 : ℝ)) x + m ^ 2 := by
      funext x
      by_cases hx : x ∈ B
      · simp only [f₀, h₀, Set.indicator_of_mem hx, mul_one]
        have hre : ‖(1 : ℂ) - (m : ℂ)‖ ^ 2 = (1 - m) ^ 2 := by
          rw [show (1 : ℂ) - (m : ℂ) = ((1 - m : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, sq_abs]
        rw [hre]; ring
      · simp only [f₀, h₀, Set.indicator_of_notMem hx, zero_sub, norm_neg,
          Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_zero, zero_add]
    have hB_int : Integrable (B.indicator fun _ => (1 : ℝ)) (haarSU 2) :=
      (integrable_const (1 : ℝ)).indicator hB_meas
    rw [hpt, integral_add (hB_int.const_mul _) (integrable_const _),
      integral_const_mul, integral_indicator hB_meas, setIntegral_const,
      MeasureTheory.measureReal_def, integral_const]
    simp only [smul_eq_mul, mul_one, MeasureTheory.measureReal_def, measure_univ,
      ENNReal.toReal_one, one_mul]
    change (1 - 2 * m) * m + m ^ 2 ≤ m
    nlinarith [sq_nonneg m]
  have hP_iter := pb_rs_lazyP_iter_bound g hgap_spec hf₀_mem hf₀_int0 ℓ
  rcases hP_iter with ⟨hP_mem, _, hP_bound⟩
  have h_overlap : ∃ x ∈ pb_rs_ballF V⁻¹ r, ((pb_rs_lazyP g)^[ℓ] h₀) x ≠ 0 := by
    by_contra hno
    push Not at hno
    let S := pb_rs_ballF V⁻¹ r
    have hS_meas : MeasurableSet S := pb_rs_measurableSet_ballF V⁻¹ r
    have hS_m : (haarSU 2).real S = m := by
      rw [MeasureTheory.measureReal_def, pb_rs_haar_ballF_eq V⁻¹ r]
    have hP_int_sq : Integrable (fun x => ‖((pb_rs_lazyP g)^[ℓ] f₀) x‖ ^ 2) (haarSU 2) :=
      hP_mem.norm.integrable_sq
    have hset_eq : ∫ x in S, ‖((pb_rs_lazyP g)^[ℓ] f₀) x‖ ^ 2 ∂(haarSU 2) = m ^ 3 := by
      have hcongr : Set.EqOn (fun x => ‖((pb_rs_lazyP g)^[ℓ] f₀) x‖ ^ 2) (fun _ => m ^ 2) S := by
        intro x hx
        dsimp only
        have hf_eq := pb_rs_lazyP_sub_const g h₀ (m : ℂ) ℓ x
        change ((pb_rs_lazyP g)^[ℓ] f₀) x = ((pb_rs_lazyP g)^[ℓ] h₀) x - (m : ℂ) at hf_eq
        rw [hf_eq, hno x hx, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [setIntegral_congr_fun hS_meas hcongr, setIntegral_const, hS_m, smul_eq_mul]
      ring
    have hle_tot : m ^ 3 ≤ q ^ ℓ * m := by
      calc m ^ 3
          = ∫ x in S, ‖((pb_rs_lazyP g)^[ℓ] f₀) x‖ ^ 2 ∂(haarSU 2) := hset_eq.symm
        _ ≤ ∫ x, ‖((pb_rs_lazyP g)^[ℓ] f₀) x‖ ^ 2 ∂(haarSU 2) :=
            setIntegral_le_integral hP_int_sq (ae_of_all _ fun _ => sq_nonneg _)
        _ ≤ q ^ ℓ * ∫ x, ‖f₀ x‖ ^ 2 ∂(haarSU 2) := hP_bound
        _ ≤ q ^ ℓ * m := mul_le_mul_of_nonneg_left hf₀_l2 (pow_nonneg hq_pos.le ℓ)
    have hm2_le : m ^ 2 ≤ q ^ ℓ := by
      have hpow : m ^ 2 * m ≤ q ^ ℓ * m := by linarith [show m ^ 3 = m ^ 2 * m by ring]
      exact le_of_mul_le_mul_right hpow hm_pos
    exact absurd hm2_le (not_le.mpr hqℓ_lt_m2)
  obtain ⟨x, hx_ball, hx_supp⟩ := h_overlap
  obtain ⟨w, hw_len, hw_ball⟩ := pb_rs_lazyP_support_word g B ℓ x hx_supp
  refine ⟨w, ?_, ?_⟩
  · have h12 : 1 / δ > 2 := by
      rw [gt_iff_lt, lt_div_iff₀ hδ0]
      linarith
    have hlog_pos : Real.log 2 < Real.log (1 / δ) := Real.log_lt_log (by norm_num) h12
    have hlog35 : Real.log (35 / (2 * δ)) ≤ Real.log 35 + Real.log (1 / δ) := by
      rw [show 35 / (2 * δ) = (35 / 2 : ℝ) * (1 / δ) by ring, Real.log_mul (by norm_num) (by positivity)]
      have : Real.log (35 / 2 : ℝ) ≤ Real.log 35 := Real.log_le_log (by norm_num) (by norm_num)
      linarith
    have h1_le : 1 ≤ Real.log (1 / δ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2_pos]
      linarith
    have hlog35' : Real.log (35 / (2 * δ)) ≤ (Real.log 35 / Real.log 2 + 1) * Real.log (1 / δ) := by
      calc Real.log (35 / (2 * δ))
          ≤ Real.log 35 * 1 + Real.log (1 / δ) := by linarith
        _ ≤ Real.log 35 * (Real.log (1 / δ) / Real.log 2) + Real.log (1 / δ) := by
            gcongr
        _ = (Real.log 35 / Real.log 2 + 1) * Real.log (1 / δ) := by ring
    have hℓ_le : (ℓ : ℝ) ≤ 8 * Real.log (35 / (2 * δ)) / Real.log (1 / q) + 2 := by
      have hceil : (Nat.ceil (8 * Real.log (35 / (2 * δ)) / Real.log (1 / q)) : ℝ) <
          8 * Real.log (35 / (2 * δ)) / Real.log (1 / q) + 1 :=
        Nat.ceil_lt_add_one (by
          apply div_nonneg _ hlog1q_pos.le
          apply mul_nonneg (by norm_num)
          exact Real.log_nonneg (by
            have : 1 ≤ 35 / (2 * δ) := by rw [le_div_iff₀ (by positivity)]; linarith
            exact this))
      have hℓ_eq : (ℓ : ℝ) = (Nat.ceil (8 * Real.log (35 / (2 * δ)) / Real.log (1 / q)) : ℝ) + 1 := by
        push_cast [ℓ]; rfl
      linarith
    have hw_real : (w.length : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hw_len
    have hA_term : A_c * Real.log (35 / (2 * δ)) ≤
        A_c * ((Real.log 35 / Real.log 2 + 1) * Real.log (1 / δ)) :=
      mul_le_mul_of_nonneg_left hlog35' hAc_pos.le
    have h2_term : (2 : ℝ) ≤ 2 * (Real.log (1 / δ) / Real.log 2) := by linarith
    calc (w.length : ℝ)
        ≤ (ℓ : ℝ) := hw_real
      _ ≤ A_c * Real.log (35 / (2 * δ)) + 2 := by
          have : 8 * Real.log (35 / (2 * δ)) / Real.log (1 / q) = A_c * Real.log (35 / (2 * δ)) := by
            simp [A_c]; ring
          linarith
      _ ≤ A_c * ((Real.log 35 / Real.log 2 + 1) * Real.log (1 / δ)) +
            2 * (Real.log (1 / δ) / Real.log 2) := add_le_add hA_term h2_term
      _ = C_su2 * Real.log (1 / δ) := by simp [C_su2]; ring
  · set W : SU 2 := pb_rs_evalWord g w
    have hWx : pb_rs_frobSq ((W : Matrix (Fin 2) (Fin 2) ℂ) -
        ((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ)) < r ^ 2 := by
      have hsub : (W : Matrix (Fin 2) (Fin 2) ℂ) - ((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) =
          (((W * x : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) *
            ((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) := by
        change (W : Matrix (Fin 2) (Fin 2) ℂ) - ((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) =
          ((W : Matrix (Fin 2) (Fin 2) ℂ) * (x : Matrix (Fin 2) (Fin 2) ℂ) - 1) *
            ((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ)
        have hxx : (x : Matrix (Fin 2) (Fin 2) ℂ) * ((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
          change ((x * x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) = 1
          simp
        rw [sub_mul, Matrix.mul_assoc, hxx, Matrix.mul_one, one_mul]
      rw [hsub, pb_rs_frobSq_mul_unitary_right (Matrix.specialUnitaryGroup_le_unitaryGroup x⁻¹.2)]
      exact hw_ball
    have hxV : pb_rs_frobSq (((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) -
        (V : Matrix (Fin 2) (Fin 2) ℂ)) < r ^ 2 := by
      have hconj : ((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) - (V : Matrix (Fin 2) (Fin 2) ℂ) =
          ((x : Matrix (Fin 2) (Fin 2) ℂ) - ((V⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
        have hxinv : ((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) =
            (x : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := rfl
        have hVinv : ((V⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) =
            (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := rfl
        rw [hxinv, hVinv, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
      rw [hconj, pb_rs_frobSq_conjTranspose]
      exact hx_ball
    have hWV_frob : pb_rs_frobSq ((W : Matrix (Fin 2) (Fin 2) ℂ) -
        (V : Matrix (Fin 2) (Fin 2) ℂ)) < δ ^ 2 := by
      have hsplit : (W : Matrix (Fin 2) (Fin 2) ℂ) - (V : Matrix (Fin 2) (Fin 2) ℂ) =
          ((W : Matrix (Fin 2) (Fin 2) ℂ) - ((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ)) +
          (((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) - (V : Matrix (Fin 2) (Fin 2) ℂ)) := by
        abel
      rw [hsplit]
      have hle := pb_rs_frobSq_add_le
        ((W : Matrix (Fin 2) (Fin 2) ℂ) - ((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ))
        (((x⁻¹ : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) - (V : Matrix (Fin 2) (Fin 2) ℂ))
      have hr_eq : 4 * r ^ 2 = δ ^ 2 := by simp [r]; ring
      linarith
    have hspec : specNorm ((W : Matrix (Fin 2) (Fin 2) ℂ) - (V : Matrix (Fin 2) (Fin 2) ℂ)) ≤
        Real.sqrt (pb_rs_frobSq ((W : Matrix (Fin 2) (Fin 2) ℂ) -
          (V : Matrix (Fin 2) (Fin 2) ℂ))) :=
      pb_rs_specNorm_le_sqrt_sum_sq _
    exact hspec.trans ((Real.sqrt_le_iff.mpr ⟨hδ0.le, hWV_frob.le⟩))

/-! ### 5. Circuit unitaries, lifting 1-qubit to 2-qubit, and main synthesis -/

private lemma pb_rs_hadamard_mem_unitary : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star hadamard = hadamard := by
    ext a b; cases a <;> cases b <;> simp [hadamard, Complex.conj_ofReal]
  rw [hstar, hadamard_mul_self]

private lemma pb_rs_gateT_mem_unitary : gateT ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  cases a <;> cases b <;> simp [gateT, Matrix.mul_apply]
  rw [show Complex.I * ↑Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    ← Complex.exp_conj]
  have hconj : (starRingEnd ℂ) (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
      -(((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj, ← Complex.exp_add]
  simp

private lemma pb_rs_cnot_mem_unitary : cnot ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    simp [cnot, Matrix.mul_apply, Fintype.sum_prod_type]

private lemma pb_rs_rot_mem_unitary (θ : ℝ) : rot θ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  cases a <;> cases b <;> simp [rot, Matrix.mul_apply]
  rw [← Complex.exp_conj]
  have hconj : (starRingEnd ℂ) ((θ : ℂ) * Complex.I) = -((θ : ℂ) * Complex.I) := by simp
  rw [hconj, ← Complex.exp_add]
  simp

private lemma pb_rs_ofMatrix1_unitary {M : Matrix Bool Bool ℂ}
    (hM : M ∈ Matrix.unitaryGroup Bool ℂ) : (Gate.ofMatrix1 M).IsUnitary := by
  dsimp only [Gate.IsUnitary, Gate.ofMatrix1]
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  ext y z
  have hm := congrFun (congrFun hM (y 0)) (z 0)
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply, Matrix.one_apply] at hm ⊢
  have hsum : (∑ j : Qubits 1, M (y 0) (j 0) * star (M (z 0) (j 0))) =
      ∑ b : Bool, M (y 0) b * star (M (z 0) b) :=
    Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool)
      (fun j : Qubits 1 => M (y 0) (j 0) * star (M (z 0) (j 0)))
      (fun b : Bool => M (y 0) b * star (M (z 0) b)) (fun _ => rfl)
  rw [hsum, hm]
  by_cases hyz : y = z
  · subst hyz; simp
  · have h0 : y 0 ≠ z 0 := fun h => hyz (funext fun i => by rw [Fin.eq_zero i]; exact h)
    simp [hyz, h0]

private lemma pb_rs_ofMatrix2_unitary {M : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) : (Gate.ofMatrix2 M).IsUnitary := by
  dsimp only [Gate.IsUnitary, Gate.ofMatrix2]
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  ext y z
  let e2 : Qubits 2 ≃ Bool × Bool :=
    { toFun := fun x => (x 0, x 1)
      invFun := fun p => ![p.1, p.2]
      left_inv := fun x => funext fun i => by fin_cases i <;> rfl
      right_inv := fun _ => rfl }
  have hm := congrFun (congrFun hM (e2 y)) (e2 z)
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply, Matrix.one_apply] at hm ⊢
  have hsum : (∑ j : Qubits 2, M (y 0, y 1) (j 0, j 1) * star (M (z 0, z 1) (j 0, j 1))) =
      ∑ p : Bool × Bool, M (e2 y) p * star (M (e2 z) p) :=
    Fintype.sum_equiv e2
      (fun j : Qubits 2 => M (y 0, y 1) (j 0, j 1) * star (M (z 0, z 1) (j 0, j 1)))
      (fun p : Bool × Bool => M (e2 y) p * star (M (e2 z) p)) (fun _ => rfl)
  rw [hsum, hm]
  by_cases hyz : y = z
  · subst hyz; simp
  · have hne : e2 y ≠ e2 z := fun h => hyz (e2.injective h)
    simp [hyz, hne]

private lemma pb_rs_cliffordT_isUnitary : ∀ g ∈ CliffordT, g.IsUnitary := by
  intro g hg
  rcases hg with rfl | rfl | rfl
  · exact pb_rs_ofMatrix1_unitary pb_rs_hadamard_mem_unitary
  · exact pb_rs_ofMatrix1_unitary pb_rs_gateT_mem_unitary
  · exact pb_rs_ofMatrix2_unitary pb_rs_cnot_mem_unitary

private lemma pb_rs_hcnotrot_isUnitary : ∀ g ∈ HCnotRotGates, g.IsUnitary := by
  intro g hg
  rcases hg with (rfl | rfl) | ⟨θ, _, rfl⟩
  · exact pb_rs_ofMatrix1_unitary pb_rs_hadamard_mem_unitary
  · exact pb_rs_ofMatrix2_unitary pb_rs_cnot_mem_unitary
  · exact pb_rs_ofMatrix1_unitary (pb_rs_rot_mem_unitary θ)

private lemma pb_rs_embedOp_mul {m n : ℕ} (A B : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    let lift : Qubits m → Qubits n := fun u a =>
      if ha : a ∈ Set.range w then u (Classical.choose ha) else y a
    have hlift_w : ∀ u : Qubits m, lift u ∘ w = u := by
      intro u; funext b
      have ha : w b ∈ Set.range w := ⟨b, rfl⟩
      change (if ha' : w b ∈ Set.range w then u (Classical.choose ha') else y (w b)) = u b
      rw [dif_pos ha]
      congr 1
      exact w.injective (Classical.choose_spec ha)
    have hlift_off : ∀ u : Qubits m, ∀ a : Fin n, a ∉ Set.range w → lift u a = y a := by
      intro u a ha
      change (if ha' : a ∈ Set.range w then u (Classical.choose ha') else y a) = y a
      rw [dif_neg ha]
    have hzero : ∀ x : Qubits n, x ∉ Set.range lift →
        (if ∀ a : Fin n, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
        (if ∀ a : Fin n, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0) = 0 := by
      intro x hx
      by_cases hxy : ∀ a : Fin n, a ∉ Set.range w → y a = x a
      · exfalso; apply hx; refine ⟨x ∘ w, ?_⟩
        funext a
        by_cases ha : a ∈ Set.range w
        · obtain ⟨b, rfl⟩ := ha
          have hb : w b ∈ Set.range w := ⟨b, rfl⟩
          change (if ha' : w b ∈ Set.range w then (x ∘ w) (Classical.choose ha') else y (w b)) = x (w b)
          rw [dif_pos hb]
          change x (w (Classical.choose hb)) = x (w b)
          rw [Classical.choose_spec hb]
        · change (if ha' : a ∈ Set.range w then (x ∘ w) (Classical.choose ha') else y a) = x a
          rw [dif_neg ha]
          exact hxy a ha
      · rw [if_neg hxy, zero_mul]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image lift))
        (fun x _ hx => hzero x (by simpa using hx)),
      Finset.sum_image (fun u _ v _ huv => by
        have := congrArg (· ∘ w) huv
        simpa [hlift_w] using this)]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hyu : ∀ a : Fin n, a ∉ Set.range w → y a = lift u a := fun a ha => (hlift_off u a ha).symm
    have huz : ∀ a : Fin n, a ∉ Set.range w → lift u a = z a := fun a ha =>
      (hlift_off u a ha).trans (hyz a ha)
    rw [if_pos hyu, if_pos huz, hlift_w]
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h1 : ∀ a : Fin n, a ∉ Set.range w → y a = x a
    · have h2 : ¬ ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun h2 =>
        hyz fun a ha => (h1 a ha).trans (h2 a ha)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

private lemma pb_rs_embedOp_conjTranspose {m n : ℕ} (M : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp Mᴴ w = (embedOp M w)ᴴ := by
  ext y z
  simp only [embedOp, Matrix.conjTranspose_apply, Matrix.of_apply]
  have hc : (∀ a : Fin n, a ∉ Set.range w → y a = z a) ↔
      (∀ a : Fin n, a ∉ Set.range w → z a = y a) :=
    ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos h, if_pos (hc.mp h)]
  · rw [if_neg h, if_neg (mt hc.mpr h), star_zero]

private lemma pb_rs_embedOp_trans {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (u : Fin k ↪ Fin m) (w : Fin m ↪ Fin n) :
    embedOp (embedOp M u) w = embedOp M (u.trans w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  have hiff : ((∀ a : Fin n, a ∉ Set.range w → y a = z a) ∧
      (∀ b : Fin m, b ∉ Set.range u → (y ∘ w) b = (z ∘ w) b)) ↔
      (∀ a : Fin n, a ∉ Set.range (u.trans w) → y a = z a) := by
    constructor
    · rintro ⟨hw, hu⟩ a ha
      by_cases haw : a ∈ Set.range w
      · obtain ⟨b, rfl⟩ := haw
        have hbu : b ∉ Set.range u := fun ⟨c, hc⟩ => ha ⟨c, by simp [hc]⟩
        exact hu b hbu
      · exact hw a haw
    · intro h
      refine ⟨fun a haw => h a (fun ⟨c, hc⟩ => haw ⟨u c, hc⟩), fun b hbu => ?_⟩
      exact h (w b) (fun ⟨c, hc⟩ => hbu ⟨c, w.injective (by simpa using hc)⟩)
  by_cases hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · by_cases hu : ∀ b : Fin m, b ∉ Set.range u → (y ∘ w) b = (z ∘ w) b
    · rw [if_pos hw, if_pos hu, if_pos (hiff.mp ⟨hw, hu⟩)]
      rfl
    · rw [if_pos hw, if_neg hu, if_neg (fun h => hu (hiff.mpr h).2)]
  · rw [if_neg hw, if_neg (fun h => hw (hiff.mpr h).1)]

private lemma pb_rs_embedOp_isUnitary {m n : ℕ} {M : Matrix (Qubits m) (Qubits m) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Qubits m) ℂ) (w : Fin m ↪ Fin n) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hM ⊢
  rw [← pb_rs_embedOp_conjTranspose, ← pb_rs_embedOp_mul, hM, embedOp_one]

private lemma pb_rs_circuit_unitary_cons {S : Set Gate} {n : ℕ}
    (g : GateApp S n) (c : Circuit S n) :
    Circuit.unitary (g :: c) = Circuit.unitary c * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

private lemma pb_rs_circuit_unitary_append {S : Set Gate} {n : ℕ}
    (c₁ c₂ : Circuit S n) :
    Circuit.unitary (c₁ ++ c₂) = Circuit.unitary c₂ * Circuit.unitary c₁ := by
  simp [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

private lemma pb_rs_circuit_unitary_mem {S : Set Gate} {n : ℕ}
    (hS : ∀ g ∈ S, g.IsUnitary) (c : Circuit S n) :
    c.unitary ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  induction c with
  | nil => simp [Circuit.unitary]
  | cons g gs ih =>
    rw [pb_rs_circuit_unitary_cons]
    exact mul_mem ih (pb_rs_embedOp_isUnitary (hS g.gate g.mem) g.wires)

private lemma pb_rs_circuit_map_wires {S : Set Gate} {m n : ℕ}
    (c : Circuit S m) (w : Fin m ↪ Fin n) :
    Circuit.unitary (c.map fun g => (⟨g.gate, g.mem, g.wires.trans w⟩ : GateApp S n)) =
      embedOp c.unitary w := by
  induction c with
  | nil => simp [Circuit.unitary, embedOp_one]
  | cons g gs ih =>
    rw [List.map_cons, pb_rs_circuit_unitary_cons, ih]
    change embedOp (Circuit.unitary gs) w * embedOp g.gate.mat (g.wires.trans w) = _
    rw [← pb_rs_embedOp_trans, ← pb_rs_embedOp_mul, pb_rs_circuit_unitary_cons]

private lemma pb_rs_embedOp_sub {m n : ℕ} (A B : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp (A - B) w = embedOp A w - embedOp B w := by
  ext y z
  simp only [embedOp, Matrix.sub_apply, Matrix.of_apply]
  split_ifs <;> simp

private lemma pb_rs_embedOp_smul {m n : ℕ} (a : ℂ) (A : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp (a • A) w = a • embedOp A w := by
  ext y z
  simp only [embedOp, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> simp

private lemma pb_rs_specNorm_embedOp_wire1_two (D : Matrix (Qubits 1) (Qubits 1) ℂ)
    (w : Fin 1 ↪ Fin 2) :
    specNorm (embedOp D w) ≤ specNorm D := by
  let _inst1 : NormedAddCommGroup (Matrix (Qubits 1) (Qubits 1) ℂ) := Matrix.instL2OpNormedAddCommGroup
  let _inst2 : NormedAddCommGroup (Matrix (Qubits 2) (Qubits 2) ℂ) := Matrix.instL2OpNormedAddCommGroup
  have hD_nonneg : 0 ≤ specNorm D := by
    rw [specNorm, ← Matrix.l2_opNorm_toEuclideanCLM]
    exact norm_nonneg _
  rw [specNorm, ← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hD_nonneg fun x => ?_
  let q : Fin 2 := w 0
  let q' : Fin 2 := if q = 0 then 1 else 0
  have hqq' : q ≠ q' := by
    dsimp [q']
    split_ifs with h
    · rw [h]; decide
    · exact h
  have h_eq_or : ∀ a : Fin 2, a = q ∨ a = q' := by
    intro a
    dsimp [q']
    split_ifs with h
    · have ha : a.val < 2 := a.isLt
      fin_cases a
      · left; exact h.symm
      · right; rfl
    · have hq1 : q = 1 := Fin.ext (by omega)
      fin_cases a
      · right; rfl
      · left; exact hq1.symm
  have h_not_range : ∀ a : Fin 2, a ∉ Set.range w ↔ a = q' := by
    intro a
    constructor
    · intro ha
      have hne : a ≠ q := fun h => ha ⟨0, h.symm⟩
      rcases h_eq_or a with rfl | rfl
      · exact absurd rfl hne
      · rfl
    · intro ha ⟨i, hi⟩
      rw [Fin.eq_zero i] at hi
      exact hqq' (hi.trans ha)
  let eSplit : Qubits 2 ≃ Bool × Qubits 1 :=
    { toFun := fun y => (y q', fun _ => y q)
      invFun := fun p a => if a = q then p.2 0 else p.1
      left_inv := fun y => funext fun a => by
        by_cases ha : a = q
        · simp [ha]
        · have ha' : a = q' := (h_not_range a).mp fun ⟨i, hi⟩ =>
            ha (by rw [Fin.eq_zero i] at hi; exact hi.symm)
          change (if a = q then y q else y q') = y a
          rw [ha', if_neg hqq'.symm]
      right_inv := fun ⟨b, u⟩ =>
        Prod.ext (by simp [hqq'.symm]) (funext fun i => by simp [Fin.eq_zero i]) }
  let slice : Bool → EuclideanSpace ℂ (Qubits 1) := fun b =>
    WithLp.toLp 2 (fun u => x (eSplit.symm (b, u)))
  have hx_sq : ‖x‖ ^ 2 = ‖slice false‖ ^ 2 + ‖slice true‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [← Fintype.sum_equiv eSplit.symm (fun p : Bool × Qubits 1 => ‖x (eSplit.symm p)‖ ^ 2)
      (fun z : Qubits 2 => ‖x z‖ ^ 2) (fun _ => rfl)]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  have hact_pt : ∀ y : Qubits 2,
      (Matrix.toEuclideanCLM (n := Qubits 2) (𝕜 := ℂ) (embedOp D w) x) y =
        (Matrix.toEuclideanCLM (n := Qubits 1) (𝕜 := ℂ) D (slice (y q'))) (fun _ => y q) := by
    intro y
    change ∑ z : Qubits 2,
      (if ∀ a : Fin 2, a ∉ Set.range w → y a = z a then D (y ∘ w) (z ∘ w) else 0) * x z =
      ∑ u : Qubits 1, D (fun _ => y q) u * (slice (y q')) u
    rw [← Fintype.sum_equiv eSplit.symm
      (fun p : Bool × Qubits 1 => (if ∀ a : Fin 2, a ∉ Set.range w → y a = (eSplit.symm p) a
        then D (y ∘ w) ((eSplit.symm p) ∘ w) else 0) * x (eSplit.symm p))
      (fun z : Qubits 2 => (if ∀ a : Fin 2, a ∉ Set.range w → y a = z a
        then D (y ∘ w) (z ∘ w) else 0) * x z)
      (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (y q') (fun b _ hb => by
      refine Finset.sum_eq_zero fun u _ => ?_
      have hfail : ¬ ∀ a : Fin 2, a ∉ Set.range w → y a = (eSplit.symm (b, u)) a := fun h => by
        have hq' := h q' ((h_not_range q').mpr rfl)
        have hsymm : (eSplit.symm (b, u)) q' = b := by simp [eSplit, hqq'.symm]
        exact hb (hq'.trans hsymm).symm
      rw [if_neg hfail, zero_mul]) (fun h => absurd (Finset.mem_univ _) h)]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hok : ∀ a : Fin 2, a ∉ Set.range w → y a = (eSplit.symm (y q', u)) a := by
      intro a ha
      rw [(h_not_range a).mp ha]
      simp [eSplit, hqq'.symm]
    have hyw : y ∘ w = fun _ => y q := funext fun i => by rw [Fin.eq_zero i]; rfl
    have huw : (eSplit.symm (y q', u)) ∘ w = u := funext fun i => by
      have hi : w i = q := by rw [Fin.eq_zero i]
      change (if w i = q then u 0 else y q') = u i
      rw [if_pos hi, Fin.eq_zero i]
    rw [if_pos hok, hyw, huw]
  have hact_sq : ‖Matrix.toEuclideanCLM (n := Qubits 2) (𝕜 := ℂ) (embedOp D w) x‖ ^ 2 =
      ‖Matrix.toEuclideanCLM (n := Qubits 1) (𝕜 := ℂ) D (slice false)‖ ^ 2 +
      ‖Matrix.toEuclideanCLM (n := Qubits 1) (𝕜 := ℂ) D (slice true)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp_rw [hact_pt]
    rw [← Fintype.sum_equiv eSplit.symm
      (fun p : Bool × Qubits 1 => ‖(Matrix.toEuclideanCLM (n := Qubits 1) (𝕜 := ℂ) D (slice p.1)) p.2‖ ^ 2)
      (fun y : Qubits 2 => ‖(Matrix.toEuclideanCLM (n := Qubits 1) (𝕜 := ℂ) D (slice (y q')))
        (fun _ => y q)‖ ^ 2)
      (fun p => by
        have hp1 : (eSplit.symm p) q' = p.1 := by simp [eSplit, hqq'.symm]
        have hp2 : (fun _ : Fin 1 => (eSplit.symm p) q) = p.2 := funext fun i => by
          simp [eSplit, Fin.eq_zero i]
        rw [hp1, hp2])]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  have hbound : ‖Matrix.toEuclideanCLM (n := Qubits 2) (𝕜 := ℂ) (embedOp D w) x‖ ^ 2 ≤
      (specNorm D * ‖x‖) ^ 2 := by
    have hb0 : ‖Matrix.toEuclideanCLM (n := Qubits 1) (𝕜 := ℂ) D (slice false)‖ ≤
        specNorm D * ‖slice false‖ := by
      rw [specNorm, ← Matrix.l2_opNorm_toEuclideanCLM]
      exact (Matrix.toEuclideanCLM (n := Qubits 1) (𝕜 := ℂ) D).le_opNorm (slice false)
    have hb1 : ‖Matrix.toEuclideanCLM (n := Qubits 1) (𝕜 := ℂ) D (slice true)‖ ≤
        specNorm D * ‖slice true‖ := by
      rw [specNorm, ← Matrix.l2_opNorm_toEuclideanCLM]
      exact (Matrix.toEuclideanCLM (n := Qubits 1) (𝕜 := ℂ) D).le_opNorm (slice true)
    have hs0 : ‖Matrix.toEuclideanCLM (n := Qubits 1) (𝕜 := ℂ) D (slice false)‖ ^ 2 ≤
        (specNorm D) ^ 2 * ‖slice false‖ ^ 2 := by
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hb0 2]
    have hs1 : ‖Matrix.toEuclideanCLM (n := Qubits 1) (𝕜 := ℂ) D (slice true)‖ ^ 2 ≤
        (specNorm D) ^ 2 * ‖slice true‖ ^ 2 := by
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hb1 2]
    rw [hact_sq, mul_pow, hx_sq]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD_nonneg (norm_nonneg x))).mp hbound

private lemma pb_rs_approxUpToPhase_refl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    ApproxUpToPhase U U ε := by
  let _inst : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.instL2OpNormedAddCommGroup
  refine ⟨0, ?_⟩
  simpa [specNorm] using hε

private lemma pb_rs_approxUpToPhase_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Matrix ι ι ℂ} {ε₁ ε₂ : ℝ} (h : ApproxUpToPhase U V ε₁) (hle : ε₁ ≤ ε₂) :
    ApproxUpToPhase U V ε₂ := by
  obtain ⟨θ, hθ⟩ := h
  exact ⟨θ, hθ.trans hle⟩

private lemma pb_rs_approxUpToPhase_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U₁ U₂ V₁ V₂ : Matrix ι ι ℂ} {ε₁ ε₂ : ℝ}
    (hU₁ : U₁ ∈ Matrix.unitaryGroup ι ℂ) (hV₂ : V₂ ∈ Matrix.unitaryGroup ι ℂ)
    (h₁ : ApproxUpToPhase U₁ V₁ ε₁) (h₂ : ApproxUpToPhase U₂ V₂ ε₂) :
    ApproxUpToPhase (U₂ * U₁) (V₂ * V₁) (ε₁ + ε₂) := by
  obtain ⟨θ₁, hθ₁⟩ := h₁
  obtain ⟨θ₂, hθ₂⟩ := h₂
  refine ⟨θ₁ + θ₂, ?_⟩
  let a : ℂ := Complex.exp ((θ₂ : ℂ) * Complex.I)
  let b : ℂ := Complex.exp ((θ₁ : ℂ) * Complex.I)
  have hab : Complex.exp (((θ₁ + θ₂ : ℝ) : ℂ) * Complex.I) = a * b := by
    dsimp [a, b]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hdecomp : U₂ * U₁ - Complex.exp (((θ₁ + θ₂ : ℝ) : ℂ) * Complex.I) • (V₂ * V₁) =
      (U₂ - a • V₂) * U₁ + (a • V₂) * (U₁ - b • V₁) := by
    rw [hab, mul_comm a b]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
    abel
  rw [hdecomp]
  have ha_norm : ‖a‖ = 1 := Complex.norm_exp_ofReal_mul_I θ₂
  have hU₁_norm : specNorm U₁ ≤ 1 := pb_rs_specNorm_unitary_le_one hU₁
  have hV₂_norm : specNorm V₂ ≤ 1 := pb_rs_specNorm_unitary_le_one hV₂
  have haV₂_norm : specNorm (a • V₂) ≤ 1 := by
    rw [pb_rs_specNorm_smul, ha_norm, one_mul]
    exact hV₂_norm
  have h1_nonneg : 0 ≤ specNorm (U₁ - b • V₁) := by
    rw [specNorm, ← Matrix.l2_opNorm_toEuclideanCLM]; exact norm_nonneg _
  have h2_nonneg : 0 ≤ specNorm (U₂ - a • V₂) := by
    rw [specNorm, ← Matrix.l2_opNorm_toEuclideanCLM]; exact norm_nonneg _
  calc specNorm ((U₂ - a • V₂) * U₁ + (a • V₂) * (U₁ - b • V₁))
      ≤ specNorm ((U₂ - a • V₂) * U₁) + specNorm ((a • V₂) * (U₁ - b • V₁)) :=
        pb_rs_specNorm_add_le _ _
    _ ≤ specNorm (U₂ - a • V₂) * specNorm U₁ + specNorm (a • V₂) * specNorm (U₁ - b • V₁) :=
        add_le_add (pb_rs_specNorm_mul_le _ _) (pb_rs_specNorm_mul_le _ _)
    _ ≤ ε₂ * 1 + 1 * ε₁ := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul hθ₂ hU₁_norm
            (by rw [specNorm, ← Matrix.l2_opNorm_toEuclideanCLM]; exact norm_nonneg _)
            (h2_nonneg.trans hθ₂)
        · exact mul_le_mul haV₂_norm hθ₁ h1_nonneg zero_le_one
    _ = ε₁ + ε₂ := by ring

private lemma pb_rs_submatrix_unitary_mem {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {U : Matrix κ κ ℂ}
    (hU : U ∈ Matrix.unitaryGroup κ ℂ) :
    U.submatrix e e ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  ext i j
  have hij := congrFun (congrFun hU (e i)) (e j)
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply, Matrix.one_apply] at hij ⊢
  have hsum : (∑ k : κ, U (e i) k * star (U (e j) k)) =
      ∑ l : ι, U (e i) (e l) * star (U (e j) (e l)) :=
    (Fintype.sum_equiv e (fun l : ι => U (e i) (e l) * star (U (e j) (e l)))
      (fun k : κ => U (e i) k * star (U (e j) k)) (fun _ => rfl)).symm
  rw [← hsum, hij]
  simp [e.injective.eq_iff]

private lemma pb_rs_synth_one_qubit (g : Fin 2 → SU 2)
    (hgap : HasSpectralGap (haarSU 2) g)
    (e : Fin 2 ≃ Qubits 1)
    (hword : ∀ w : List (Bool × Fin 2),
      ∃ (c : Circuit CliffordT 1) (θ : ℝ),
        c.size ≤ 7 * w.length ∧
        (((pb_rs_evalWord g w : SU 2) : Matrix (Fin 2) (Fin 2) ℂ)).submatrix e.symm e.symm =
          Complex.exp ((θ : ℂ) * Complex.I) • c.unitary) :
    ∃ C_su2 : ℝ, 0 < C_su2 ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      ∀ U : Matrix (Qubits 1) (Qubits 1) ℂ, U ∈ Matrix.unitaryGroup (Qubits 1) ℂ →
        ∃ c : Circuit CliffordT 1,
          (c.size : ℝ) ≤ (7 * C_su2) * Real.log (1 / δ) ∧ ApproxUpToPhase U c.unitary δ := by
  obtain ⟨C_su2, hC_pos, h_su2⟩ := pb_rs_su2_approx_of_gap g hgap
  refine ⟨C_su2, hC_pos, fun δ hδ0 hδ12 U hU => ?_⟩
  let U₂ : Matrix (Fin 2) (Fin 2) ℂ := U.submatrix e e
  have hU₂ : U₂ ∈ Matrix.unitaryGroup (Fin 2) ℂ := pb_rs_submatrix_unitary_mem e hU
  have hU₂_mul : U₂ * star U₂ = 1 := Matrix.mem_unitaryGroup_iff.mp hU₂
  have hdet_mul : U₂.det * star U₂.det = 1 := by
    calc U₂.det * star U₂.det
        = U₂.det * (U₂ᴴ).det := by simp [Matrix.det_conjTranspose]
      _ = (U₂ * U₂ᴴ).det := (Matrix.det_mul U₂ U₂ᴴ).symm
      _ = (1 : Matrix (Fin 2) (Fin 2) ℂ).det := by rw [← Matrix.star_eq_conjTranspose, hU₂_mul]
      _ = 1 := Matrix.det_one
  have hdet_norm : ‖U₂.det‖ = 1 := by
    have hsq : ‖U₂.det‖ ^ 2 = 1 := by
      have hre := congrArg Complex.re hdet_mul
      have hmul : U₂.det * star U₂.det = ((‖U₂.det‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
      rw [hmul, Complex.ofReal_re, Complex.one_re] at hre
      exact hre
    nlinarith [norm_nonneg U₂.det]
  let φ : ℝ := U₂.det.arg
  have hdet_exp : U₂.det = Complex.exp ((φ : ℂ) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I U₂.det
    rw [hdet_norm, Complex.ofReal_one, one_mul] at h
    exact h.symm
  let α : ℝ := -φ / 2
  let V₂ : Matrix (Fin 2) (Fin 2) ℂ := Complex.exp ((α : ℂ) * Complex.I) • U₂
  have hV₂_unitary : V₂ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hphase : Complex.exp ((α : ℂ) * Complex.I) * star (Complex.exp ((α : ℂ) * Complex.I)) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj]
      have hconj : (starRingEnd ℂ) ((α : ℂ) * Complex.I) = -((α : ℂ) * Complex.I) := by simp
      rw [hconj, ← Complex.exp_add]
      simp
    have hstar : star V₂ = star (Complex.exp ((α : ℂ) * Complex.I)) • star U₂ := by
      ext i j; simp [V₂, Matrix.star_apply, mul_comm]
    dsimp [V₂]
    rw [hstar, smul_mul_smul_comm, hphase, one_smul, hU₂_mul]
  have hV₂_det : V₂.det = 1 := by
    dsimp [V₂]
    rw [Matrix.det_smul, Fintype.card_fin, hdet_exp, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have hzero : ((2 : ℕ) : ℂ) * ((α : ℂ) * Complex.I) + (φ : ℂ) * Complex.I = 0 := by
      dsimp [α]; push_cast; ring
    rw [hzero, Complex.exp_zero]
  let V : SU 2 := ⟨V₂, hV₂_unitary, hV₂_det⟩
  obtain ⟨w, hw_len, hw_spec⟩ := h_su2 δ hδ0 hδ12 V
  obtain ⟨c, θ_word, hc_size, hc_eq⟩ := hword w
  refine ⟨c, ?_, ?_⟩
  · have hc_real : (c.size : ℝ) ≤ 7 * (w.length : ℝ) := by exact_mod_cast hc_size
    linarith
  · refine ⟨θ_word - α, ?_⟩
    have hV₂_sub : V₂.submatrix e.symm e.symm = Complex.exp ((α : ℂ) * Complex.I) • U := by
      ext y z
      simp [V₂, U₂]
    have hdiff_sub : (((pb_rs_evalWord g w : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) - V₂).submatrix
        e.symm e.symm =
        Complex.exp ((θ_word : ℂ) * Complex.I) • c.unitary -
          Complex.exp ((α : ℂ) * Complex.I) • U := by
      ext y z
      have h1 := congrFun (congrFun hc_eq y) z
      have h2 := congrFun (congrFun hV₂_sub y) z
      simp only [Matrix.submatrix_apply, Matrix.sub_apply] at h1 h2 ⊢
      rw [h1, h2]
    have hgoal_eq : U - Complex.exp (((θ_word - α : ℝ) : ℂ) * Complex.I) • c.unitary =
        -(Complex.exp ((-α : ℂ) * Complex.I) •
          ((((pb_rs_evalWord g w : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) - V₂).submatrix
            e.symm e.symm)) := by
      rw [hdiff_sub, smul_sub, smul_smul, smul_smul, ← Complex.exp_add, ← Complex.exp_add]
      have h0 : (-α : ℂ) * Complex.I + (α : ℂ) * Complex.I = 0 := by ring
      have hθ : (-α : ℂ) * Complex.I + (θ_word : ℂ) * Complex.I =
          ((θ_word - α : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [h0, hθ, Complex.exp_zero, one_smul]
      abel
    rw [hgoal_eq, pb_rs_specNorm_neg, pb_rs_specNorm_smul, ← Complex.ofReal_neg,
      Complex.norm_exp_ofReal_mul_I (-α), one_mul]
    exact (pb_rs_specNorm_submatrix_equiv e.symm _).trans hw_spec

private lemma pb_rs_compile_hcnotrot_list
    {δ B : ℝ} (hδ0 : 0 < δ) (hB1 : 1 ≤ B)
    (h1 : ∀ U₁ : Matrix (Qubits 1) (Qubits 1) ℂ, U₁ ∈ Matrix.unitaryGroup (Qubits 1) ℂ →
      ∃ c : Circuit CliffordT 1, (c.size : ℝ) ≤ B ∧ ApproxUpToPhase U₁ c.unitary δ)
    (l : Circuit HCnotRotGates 2) :
    ∃ c : Circuit CliffordT 2,
      (c.size : ℝ) ≤ (l.length : ℝ) * B ∧
      ApproxUpToPhase l.unitary c.unitary ((l.length : ℝ) * δ) := by
  induction l with
  | nil =>
    refine ⟨[], by simp [Circuit.size], pb_rs_approxUpToPhase_refl _ (by simp)⟩
  | cons g gs ih =>
    obtain ⟨c_gs, hgs_size, hgs_app⟩ := ih
    have hg_step : ∃ c_g : Circuit CliffordT 2, (c_g.size : ℝ) ≤ B ∧
        ApproxUpToPhase (embedOp g.gate.mat g.wires) c_g.unitary δ := by
      rcases g with ⟨gate, hmem, wires⟩
      rcases hmem with (rfl | rfl) | ⟨θ, _, rfl⟩
      · have hmemCT : Gate.ofMatrix1 hadamard ∈ CliffordT := by simp [CliffordT]
        refine ⟨[⟨Gate.ofMatrix1 hadamard, hmemCT, wires⟩], ?_, ?_⟩
        · simpa [Circuit.size] using hB1
        · simpa [Circuit.unitary] using pb_rs_approxUpToPhase_refl _ hδ0.le
      · have hmemCT : Gate.ofMatrix2 cnot ∈ CliffordT := by simp [CliffordT]
        refine ⟨[⟨Gate.ofMatrix2 cnot, hmemCT, wires⟩], ?_, ?_⟩
        · simpa [Circuit.size] using hB1
        · simpa [Circuit.unitary] using pb_rs_approxUpToPhase_refl _ hδ0.le
      · let U₁ : Matrix (Qubits 1) (Qubits 1) ℂ := (Gate.ofMatrix1 (rot θ)).mat
        have hU₁ : U₁ ∈ Matrix.unitaryGroup (Qubits 1) ℂ :=
          pb_rs_ofMatrix1_unitary (pb_rs_rot_mem_unitary θ)
        obtain ⟨c₁, hc₁_size, φ, hφ⟩ := h1 U₁ hU₁
        let wires1 : Fin 1 ↪ Fin 2 := wires
        let c_g : Circuit CliffordT 2 := c₁.map fun a => ⟨a.gate, a.mem, a.wires.trans wires1⟩
        refine ⟨c_g, ?_, ⟨φ, ?_⟩⟩
        · simpa [c_g, Circuit.size] using hc₁_size
        · have hc_g_u : c_g.unitary = embedOp c₁.unitary wires1 := pb_rs_circuit_map_wires c₁ wires1
          change specNorm (@embedOp 1 2 U₁ wires1 - Complex.exp ((φ : ℂ) * Complex.I) • c_g.unitary) ≤ δ
          rw [hc_g_u, ← pb_rs_embedOp_smul, ← pb_rs_embedOp_sub]
          exact (pb_rs_specNorm_embedOp_wire1_two _ wires1).trans hφ
    obtain ⟨c_g, hcg_size, hcg_app⟩ := hg_step
    refine ⟨c_g ++ c_gs, ?_, ?_⟩
    · simp only [Circuit.size, List.length_append, List.length_cons, Nat.cast_add, Nat.cast_succ] at hcg_size hgs_size ⊢
      linarith
    · change ApproxUpToPhase (Circuit.unitary ([g] ++ gs)) (c_g ++ c_gs).unitary ((g :: gs).length * δ)
      rw [pb_rs_circuit_unitary_append [g] gs, pb_rs_circuit_unitary_append c_g c_gs]
      have hg_u : Circuit.unitary ([g] : Circuit HCnotRotGates 2) = embedOp g.gate.mat g.wires := by
        simp [Circuit.unitary]
      rw [hg_u]
      have hU_mem : embedOp g.gate.mat g.wires ∈ Matrix.unitaryGroup (Qubits 2) ℂ :=
        pb_rs_embedOp_isUnitary (pb_rs_hcnotrot_isUnitary g.gate g.mem) g.wires
      have hV_mem : c_gs.unitary ∈ Matrix.unitaryGroup (Qubits 2) ℂ :=
        pb_rs_circuit_unitary_mem pb_rs_cliffordT_isUnitary c_gs
      have hmul := pb_rs_approxUpToPhase_mul hU_mem hV_mem hcg_app hgs_app
      have hlen : ((g :: gs).length : ℝ) * δ = δ + (gs.length : ℝ) * δ := by
        simp only [List.length_cons, Nat.cast_succ]
        ring
      rw [hlen]
      exact hmul

private theorem pb_rs_synthesis_of_bg
    (g : Fin 2 → SU 2)
    (halg : ∀ (j : Fin 2) (a b : Fin 2),
      IsAlgebraic ℚ ((g j : Matrix (Fin 2) (Fin 2) ℂ) a b))
    (hdense : Dense ((Subgroup.closure (Set.range g) : Subgroup (SU 2)) : Set (SU 2)))
    (e : Fin 2 ≃ Qubits 1)
    (hword : ∀ w : List (Bool × Fin 2),
      ∃ (c : Circuit CliffordT 1) (θ : ℝ),
        c.size ≤ 7 * w.length ∧
        (((pb_rs_evalWord g w : SU 2) : Matrix (Fin 2) (Fin 2) ℂ)).submatrix e.symm e.symm =
          Complex.exp ((θ : ℂ) * Complex.I) • c.unitary) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ k : ℕ, (k = 1 ∨ k = 2) →
        ∀ U : Matrix (Qubits k) (Qubits k) ℂ, U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
          ∃ c : Circuit CliffordT k,
            (c.size : ℝ) ≤ C * Real.log (1 / ε) ∧ ApproxUpToPhase U c.unitary ε := by
  have hgap : HasSpectralGap (haarSU 2) g :=
    bourgain_gamburd_SUd 2 (by norm_num) 2 (by norm_num) g halg hdense
  obtain ⟨C_su2, hC_su2, h1⟩ := pb_rs_synth_one_qubit g hgap e hword
  obtain ⟨N_dec, hdec⟩ := ConstOverheadCompile.Main.decomposition_cnot_h_rotation
  let M_dec : ℕ := max N_dec 1
  have hM1 : 1 ≤ M_dec := le_max_right N_dec 1
  have hM_real : (1 : ℝ) ≤ (M_dec : ℝ) := by exact_mod_cast hM1
  have hM_pos : (0 : ℝ) < (M_dec : ℝ) := by positivity
  have hlog4_gt1 : 1 < Real.log 4 := by
    have he4 : Real.exp 1 < (4 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) he4
  have hlog4_pos : 0 < Real.log 4 := by linarith
  let B_coeff : ℝ := max (1 / Real.log 4) (7 * C_su2)
  have hB_pos : 0 < B_coeff := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  let C : ℝ := (M_dec : ℝ) * B_coeff * (Real.log (M_dec : ℝ) + 1)
  have hlogM_nonneg : 0 ≤ Real.log (M_dec : ℝ) := Real.log_nonneg hM_real
  have hC_pos : 0 < C := by positivity
  refine ⟨C, 1 / 4, hC_pos, by norm_num, fun ε hε0 hε14 k hk U hU => ?_⟩
  have h4_lt : 4 < 1 / ε := by
    rw [lt_div_iff₀ hε0]
    linarith
  have hlog_eps_gt1 : 1 < Real.log (1 / ε) :=
    hlog4_gt1.trans (Real.log_lt_log (by norm_num) h4_lt)
  rcases hk with rfl | rfl
  · have hε12 : ε < 1 / 2 := by linarith
    obtain ⟨c, hc_size, hc_app⟩ := h1 ε hε0 hε12 U hU
    refine ⟨c, ?_, hc_app⟩
    have h7B : 7 * C_su2 ≤ B_coeff := le_max_right _ _
    have hBC : B_coeff ≤ C := by
      dsimp [C]
      have h1_le_m1 : 1 ≤ Real.log (M_dec : ℝ) + 1 := by linarith
      calc B_coeff = 1 * B_coeff * 1 := by ring
        _ ≤ (M_dec : ℝ) * B_coeff * (Real.log (M_dec : ℝ) + 1) := by
            gcongr
    have hlog_nonneg : 0 ≤ Real.log (1 / ε) := by linarith
    calc (c.size : ℝ) ≤ (7 * C_su2) * Real.log (1 / ε) := hc_size
      _ ≤ B_coeff * Real.log (1 / ε) := mul_le_mul_of_nonneg_right h7B hlog_nonneg
      _ ≤ C * Real.log (1 / ε) := mul_le_mul_of_nonneg_right hBC hlog_nonneg
  · let δ : ℝ := ε / (M_dec : ℝ)
    have hδ0 : 0 < δ := by positivity
    have hδ14 : δ < 1 / 4 := by
      calc δ = ε / (M_dec : ℝ) := rfl
        _ ≤ ε / 1 := div_le_div_of_nonneg_left hε0.le (by norm_num) hM_real
        _ = ε := div_one ε
        _ < 1 / 4 := hε14
    have hδ12 : δ < 1 / 2 := by linarith
    have h4_lt_δ : 4 < 1 / δ := by
      rw [lt_div_iff₀ hδ0]
      linarith
    have hlog4_le_δ : Real.log 4 ≤ Real.log (1 / δ) :=
      (Real.log_lt_log (by norm_num) h4_lt_δ).le
    have hlog_δ_nonneg : 0 ≤ Real.log (1 / δ) := hlog4_pos.le.trans hlog4_le_δ
    let B : ℝ := B_coeff * Real.log (1 / δ)
    have hB_nonneg : 0 ≤ B := mul_nonneg hB_pos.le hlog_δ_nonneg
    have hB1 : 1 ≤ B := by
      have h1_le : 1 ≤ (1 / Real.log 4) * Real.log (1 / δ) := by
        rw [one_div, inv_mul_eq_div, one_le_div hlog4_pos]
        exact hlog4_le_δ
      have hcoeff : 1 / Real.log 4 ≤ B_coeff := le_max_left _ _
      calc (1 : ℝ) ≤ (1 / Real.log 4) * Real.log (1 / δ) := h1_le
        _ ≤ B_coeff * Real.log (1 / δ) := mul_le_mul_of_nonneg_right hcoeff hlog_δ_nonneg
    have h1_gate : ∀ U₁ : Matrix (Qubits 1) (Qubits 1) ℂ,
        U₁ ∈ Matrix.unitaryGroup (Qubits 1) ℂ →
        ∃ c : Circuit CliffordT 1, (c.size : ℝ) ≤ B ∧ ApproxUpToPhase U₁ c.unitary δ := by
      intro U₁ hU₁
      obtain ⟨c₁, hc₁_size, hc₁_app⟩ := h1 δ hδ0 hδ12 U₁ hU₁
      refine ⟨c₁, ?_, hc₁_app⟩
      have h7B : 7 * C_su2 ≤ B_coeff := le_max_right _ _
      calc (c₁.size : ℝ) ≤ (7 * C_su2) * Real.log (1 / δ) := hc₁_size
        _ ≤ B_coeff * Real.log (1 / δ) := mul_le_mul_of_nonneg_right h7B hlog_δ_nonneg
    obtain ⟨c_dec, hcdec_size, hcdec_u⟩ := hdec 2 (Or.inr rfl) U hU
    obtain ⟨c, hc_size, hc_app⟩ := pb_rs_compile_hcnotrot_list hδ0 hB1 h1_gate c_dec
    have hcdec_le_M : (c_dec.length : ℝ) ≤ (M_dec : ℝ) := by
      have : c_dec.size ≤ M_dec := hcdec_size.trans (le_max_left N_dec 1)
      exact_mod_cast this
    refine ⟨c, ?_, ?_⟩
    · have hlog_δ : Real.log (1 / δ) = Real.log (M_dec : ℝ) + Real.log (1 / ε) := by
        rw [show 1 / δ = (M_dec : ℝ) * (1 / ε) by simp [δ]; ring,
          Real.log_mul hM_pos.ne' (by positivity)]
      have hlog_δ_le : Real.log (1 / δ) ≤ (Real.log (M_dec : ℝ) + 1) * Real.log (1 / ε) := by
        rw [hlog_δ]
        have hmul : Real.log (M_dec : ℝ) * 1 ≤ Real.log (M_dec : ℝ) * Real.log (1 / ε) :=
          mul_le_mul_of_nonneg_left hlog_eps_gt1.le hlogM_nonneg
        linarith
      calc (c.size : ℝ)
          ≤ (c_dec.length : ℝ) * B := hc_size
        _ ≤ (M_dec : ℝ) * B := mul_le_mul_of_nonneg_right hcdec_le_M hB_nonneg
        _ = (M_dec : ℝ) * B_coeff * Real.log (1 / δ) := by dsimp [B]; ring
        _ ≤ (M_dec : ℝ) * B_coeff * ((Real.log (M_dec : ℝ) + 1) * Real.log (1 / ε)) :=
            mul_le_mul_of_nonneg_left hlog_δ_le (mul_nonneg hM_pos.le hB_pos.le)
        _ = C * Real.log (1 / ε) := by dsimp [C]; ring
    · rw [hcdec_u] at hc_app
      have herr_le : (c_dec.length : ℝ) * δ ≤ ε := by
        calc (c_dec.length : ℝ) * δ
            ≤ (M_dec : ℝ) * δ := by gcongr
          _ = ε := by simp [δ]; field_simp
      exact pb_rs_approxUpToPhase_mono hc_app herr_le

end PB_HRC_RS

theorem solution :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ k : ℕ, (k = 1 ∨ k = 2) →
        ∀ U : Matrix (QAlgorithms.Qubits k) (QAlgorithms.Qubits k) ℂ,
          U ∈ Matrix.unitaryGroup (QAlgorithms.Qubits k) ℂ →
          ∃ c : QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT k,
            (c.size : ℝ) ≤ C * Real.log (1 / ε) ∧ QAlgorithms.ApproxUpToPhase U c.unitary ε :=
  pb_rs_synthesis_of_bg pb_bg_gen pb_bg_halg pb_bg_hdense pb_bg_fin2EquivQubits1
    pb_bg_word_to_circuit
