-- Prove2me | solution 1 for AutomorphicForm.valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d6d015f4-521b-5856-8967-342a209178eb

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace Ws31
namespace Torus

open AutomorphicForm Matrix

section Algebra

variable {F : Type*} [Field F]

def lin (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) : Matrix (Fin 2) (Fin 2) F := x • (1 : Matrix (Fin 2) (Fin 2) F) + y • γ

theorem lin_apply (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) (i j : Fin 2) :
    lin γ x y i j = x * (1 : Matrix (Fin 2) (Fin 2) F) i j + y * γ i j := by
  simp [lin, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem eta_fin_two (M : Matrix (Fin 2) (Fin 2) F) : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem lin_eq (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) :
    lin γ x y = !![x + y * γ 0 0, y * γ 0 1; y * γ 1 0, x + y * γ 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [lin_apply]

theorem trace_lin (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) :
    (lin γ x y).trace = 2 * x + γ.trace * y := by
  rw [lin_eq, Matrix.trace_fin_two_of, Matrix.trace_fin_two]; ring

theorem det_lin (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) :
    (lin γ x y).det = x ^ 2 + γ.trace * x * y + γ.det * y ^ 2 := by
  rw [lin_eq, Matrix.det_fin_two_of, Matrix.trace_fin_two, Matrix.det_fin_two]; ring

theorem disc_lin (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) :
    (lin γ x y).trace ^ 2 - 4 * (lin γ x y).det = y ^ 2 * (γ.trace ^ 2 - 4 * γ.det) := by
  rw [trace_lin, det_lin]; ring

theorem sq_eq_fin_two (γ : Matrix (Fin 2) (Fin 2) F) : γ * γ = γ.trace • γ - γ.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  conv_lhs => rw [eta_fin_two γ]
  rw [Matrix.mul_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Matrix.sub_apply] <;> ring

theorem lin_mul_lin (γ : Matrix (Fin 2) (Fin 2) F) (x y x' y' : F) :
    lin γ x y * lin γ x' y' = lin γ (x * x' - γ.det * y * y') (x * y' + x' * y + γ.trace * y * y') := by
  simp only [lin, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, sq_eq_fin_two, smul_sub]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

theorem lin_comm (γ : Matrix (Fin 2) (Fin 2) F) (x y x' y' : F) :
    lin γ x y * lin γ x' y' = lin γ x' y' * lin γ x y := by
  rw [lin_mul_lin, lin_mul_lin]; congr 1 <;> ring

theorem self_eq_lin (γ : Matrix (Fin 2) (Fin 2) F) : γ = lin γ 0 1 := by simp [lin]

theorem one_eq_lin (γ : Matrix (Fin 2) (Fin 2) F) : (1 : Matrix (Fin 2) (Fin 2) F) = lin γ 1 0 := by simp [lin]

theorem lin_lin_eq_self (γ : Matrix (Fin 2) (Fin 2) F) (x y : F) (hy : y ≠ 0) :
    lin (lin γ x y) (-(x / y)) (1 / y) = γ := by
  ext i j
  simp only [lin_apply]
  field_simp
  ring

theorem commute_lin_of_commute (γ M : Matrix (Fin 2) (Fin 2) F) (x y : F)
    (h : γ * M = M * γ) : lin γ x y * M = M * lin γ x y := by
  simp only [lin, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h]

theorem commute_of_commute_lin (γ M : Matrix (Fin 2) (Fin 2) F) (x y : F) (hy : y ≠ 0)
    (h : lin γ x y * M = M * lin γ x y) : γ * M = M * γ := by
  have e := lin_lin_eq_self γ x y hy
  have := commute_lin_of_commute (lin γ x y) M (-(x / y)) (1 / y) h
  rwa [e] at this

variable (γ₀ : GL (Fin 2) F) (hreg : IsRegularSemisimple γ₀)
  (hns : ∀ g : GL (Fin 2) F,
    ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
       ((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0))

include hreg hns

theorem false_of_diagonalises (P : Matrix (Fin 2) (Fin 2) F) (hP : P.det ≠ 0) (l l' : F)
    (h : (γ₀ : Matrix (Fin 2) (Fin 2) F) * P = P * !![l, 0; 0, l']) : False := by
  apply hns (Matrix.GeneralLinearGroup.mkOfDetNeZero P hP)
  have hc : (((Matrix.GeneralLinearGroup.mkOfDetNeZero P hP)⁻¹ * γ₀ * Matrix.GeneralLinearGroup.mkOfDetNeZero P hP :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![l, 0; 0, l'] := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, mul_assoc]
    show P⁻¹ * ((γ₀ : Matrix (Fin 2) (Fin 2) F) * P) = _
    rw [h, ← mul_assoc, Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP), one_mul]
  rw [hc]
  simp

omit hreg in
theorem entry01_ne_zero' (hreg : IsRegularSemisimple γ₀) : (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := by
  intro hb
  set a := (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0
  set c := (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 1
  have hγ : (γ₀ : Matrix (Fin 2) (Fin 2) F) = !![a, 0; c, d] := by
    rw [eta_fin_two (γ₀ : Matrix (Fin 2) (Fin 2) F), hb]
  have had : a - d ≠ 0 := by
    have h := (isRegularSemisimple_iff_ne_zero γ₀).mp hreg
    rw [hγ, Matrix.trace_fin_two_of, Matrix.det_fin_two_of] at h
    intro h0
    apply h
    rw [show (a + d) ^ 2 - 4 * (a * d - 0 * c) = (a - d) ^ 2 by ring, h0]; ring
  refine false_of_diagonalises γ₀ hreg hns !![a - d, 0; c, 1] ?_ a d ?_
  · rw [Matrix.det_fin_two_of]; simpa using had
  · rw [hγ, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem entry01_ne_zero : (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := entry01_ne_zero' γ₀ hns hreg

theorem charpoly_ne_zero (l : F) :
    l ^ 2 - (γ₀ : Matrix (Fin 2) (Fin 2) F).trace * l + (γ₀ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
  intro hl
  have hb := entry01_ne_zero γ₀ hreg hns
  set a := (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1 with hb'
  set c := (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have hγ : (γ₀ : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := eta_fin_two _
  rw [hγ, Matrix.trace_fin_two_of, Matrix.det_fin_two_of] at hl
  have hdisc : (a + d - 2 * l) ≠ 0 := by
    have h := (isRegularSemisimple_iff_ne_zero γ₀).mp hreg
    rw [hγ, Matrix.trace_fin_two_of, Matrix.det_fin_two_of] at h
    intro h0
    apply h
    have : (a + d) ^ 2 - 4 * (a * d - b * c) = (a + d - 2 * l) ^ 2 - 4 * (l ^ 2 - (a + d) * l + (a * d - b * c)) := by ring
    rw [this, h0, hl]; ring

  refine false_of_diagonalises γ₀ hreg hns !![b, b; l - a, a + d - l - a] ?_ l (a + d - l) ?_
  · rw [Matrix.det_fin_two_of]
    have : b * (a + d - l - a) - b * (l - a) = b * (a + d - 2 * l) := by ring
    rw [this]; exact mul_ne_zero hb hdisc
  · rw [hγ, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j
    · simp; ring
    · simp; ring
    · simp; linear_combination (-1 : F) * hl
    · simp; linear_combination (-1 : F) * hl

theorem det_lin_ne_zero (x y : F) (h : ¬ (x = 0 ∧ y = 0)) : (lin (γ₀ : Matrix (Fin 2) (Fin 2) F) x y).det ≠ 0 := by
  rw [det_lin]
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := fun hx => h ⟨hx, rfl⟩
    simpa using pow_ne_zero 2 hx
  · intro h0
    apply charpoly_ne_zero γ₀ hreg hns (-(x / y))
    field_simp
    linear_combination h0

theorem det_lin_ne_zero_of_ne_zero (x y : F) (hy : y ≠ 0) : (lin (γ₀ : Matrix (Fin 2) (Fin 2) F) x y).det ≠ 0 :=
  det_lin_ne_zero γ₀ hreg hns x y fun h => hy h.2

omit hreg hns in
theorem smul_lin (γ : Matrix (Fin 2) (Fin 2) F) (a x y : F) : a • lin γ x y = lin γ (a * x) (a * y) := by
  simp only [lin, smul_add, smul_smul]

omit hreg hns in
theorem lin_add_lin (γ : Matrix (Fin 2) (Fin 2) F) (x y x' y' : F) : lin γ x y + lin γ x' y' = lin γ (x + x') (y + y') := by
  simp only [lin, add_smul]; abel

omit hreg hns in
theorem lin_sub_smul_one (γ : Matrix (Fin 2) (Fin 2) F) (x y b : F) :
    lin γ x y - b • (1 : Matrix (Fin 2) (Fin 2) F) = lin γ (x - b) y := by
  simp only [lin, sub_smul]; abel

omit hreg hns in

theorem disc_lin_ne_zero {γ : Matrix (Fin 2) (Fin 2) F} (h : γ.trace ^ 2 - 4 * γ.det ≠ 0) (x y : F) (hy : y ≠ 0) :
    (lin γ x y).trace ^ 2 - 4 * (lin γ x y).det ≠ 0 := by
  rw [disc_lin]; exact mul_ne_zero (pow_ne_zero 2 hy) h

omit hreg in

theorem eq_lin_of_commute (hreg : IsRegularSemisimple γ₀) (M : Matrix (Fin 2) (Fin 2) F)
    (h : (γ₀ : Matrix (Fin 2) (Fin 2) F) * M = M * (γ₀ : Matrix (Fin 2) (Fin 2) F)) :
    M = lin (γ₀ : Matrix (Fin 2) (Fin 2) F)
      (M 0 0 - M 0 1 * (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 / (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1)
      (M 0 1 / (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have hb := entry01_ne_zero' γ₀ hns hreg
  set a := (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1 with hb'
  set c := (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  set p := M 0 0 with hp
  set q := M 0 1 with hq
  set r := M 1 0 with hr
  set s := M 1 1 with hs
  have hγ : (γ₀ : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := eta_fin_two _
  have hM : M = !![p, q; r, s] := eta_fin_two _
  rw [hγ, hM, Matrix.mul_fin_two, Matrix.mul_fin_two] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp at h00 h01 h10

  have hr' : r = q * c / b := by field_simp; linear_combination h00
  have hs' : s = p - q * (a - d) / b := by field_simp; linear_combination h01
  rw [hM, lin_eq, hγ]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.empty_val']
  ext i j; fin_cases i <;> fin_cases j <;> simp [hr', hs'] <;> field_simp <;> ring

theorem exists_eq_lin_of_commute (M : Matrix (Fin 2) (Fin 2) F)
    (h : (γ₀ : Matrix (Fin 2) (Fin 2) F) * M = M * (γ₀ : Matrix (Fin 2) (Fin 2) F)) :
    ∃ x y : F, M = lin (γ₀ : Matrix (Fin 2) (Fin 2) F) x y :=
  ⟨_, _, eq_lin_of_commute γ₀ hns hreg M h⟩

theorem lin_inj {x y x' y' : F} (h : lin (γ₀ : Matrix (Fin 2) (Fin 2) F) x y = lin (γ₀ : Matrix (Fin 2) (Fin 2) F) x' y') :
    x = x' ∧ y = y' := by
  have hb := entry01_ne_zero γ₀ hreg hns
  have h01 := congrFun (congrFun h 0) 1
  have h00 := congrFun (congrFun h 0) 0
  simp only [lin_apply, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.one_apply_eq, mul_zero, zero_add,
    mul_one] at h01 h00
  have hy : y = y' := mul_right_cancel₀ hb h01
  subst hy
  exact ⟨by linear_combination h00, rfl⟩

end Algebra

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
variable (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hreg : IsRegularSemisimple γ₀)
  (hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
    ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
       ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))

theorem mem_localCentralizer_iff_commute (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ localCentralizer K v γ₀ ↔
      (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * g = g * (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  rw [localCentralizer, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h; have := congrArg Units.val h; simpa [Units.val_mul] using this.symm
  · intro h; exact Units.ext (by simpa [Units.val_mul] using h.symm)

include hreg hns in

theorem mem_localCentralizer_iff (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ localCentralizer K v γ₀ ↔ ∃ x y : v.adicCompletion K,
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y := by
  rw [mem_localCentralizer_iff_commute]
  constructor
  · exact exists_eq_lin_of_commute γ₀ hreg hns _
  · rintro ⟨x, y, h⟩
    rw [h]
    exact (commute_lin_of_commute _ _ x y rfl).symm

theorem isCompact_closedBall_one : IsCompact {l : v.adicCompletion K | ‖l‖ ≤ 1} := by
  have : {l : v.adicCompletion K | ‖l‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext l; simp
  rw [this]; exact isCompact_closedBall 0 1

include hreg hns in

theorem exists_pos_forall_le_norm_charpoly :
    ∃ c : ℝ, 0 < c ∧ ∀ l : v.adicCompletion K,
      c ≤ ‖l ^ 2 - (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace * l +
          (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ∧
      c * ‖l‖ ^ 2 ≤ ‖l ^ 2 - (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace * l +
          (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ := by
  set t := (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace with ht
  set n := (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det with hn
  let χ : v.adicCompletion K → ℝ := fun l => ‖l ^ 2 - t * l + n‖
  let ρ : v.adicCompletion K → ℝ := fun m => ‖1 - t * m + n * m ^ 2‖
  have hχc : Continuous χ := by fun_prop
  have hρc : Continuous ρ := by fun_prop
  have hχ0 : ∀ l, 0 < χ l := fun l => norm_pos_iff.mpr (charpoly_ne_zero γ₀ hreg hns l)
  have hρ0 : ∀ m, 0 < ρ m := by
    intro m
    refine norm_pos_iff.mpr fun h0 => ?_
    by_cases hm : m = 0
    · subst hm; simp at h0
    · apply charpoly_ne_zero γ₀ hreg hns m⁻¹
      have : m⁻¹ ^ 2 - t * m⁻¹ + n = m⁻¹ ^ 2 * (1 - t * m + n * m ^ 2) := by field_simp
      rw [this, h0, mul_zero]
  have hB := isCompact_closedBall_one K v
  have hne : ({l : v.adicCompletion K | ‖l‖ ≤ 1}).Nonempty := ⟨0, by simp⟩
  obtain ⟨l₁, -, hmin₁⟩ := hB.exists_isMinOn hne hχc.continuousOn
  obtain ⟨m₂, -, hmin₂⟩ := hB.exists_isMinOn hne hρc.continuousOn
  set c := min (χ l₁) (ρ m₂) with hc
  have hcpos : 0 < c := lt_min (hχ0 l₁) (hρ0 m₂)
  refine ⟨c, hcpos, fun l => ?_⟩
  show c ≤ χ l ∧ c * ‖l‖ ^ 2 ≤ χ l
  by_cases hl : ‖l‖ ≤ 1
  · have h1 : c ≤ χ l := (min_le_left _ _).trans (hmin₁ hl)
    refine ⟨h1, ?_⟩
    have hl2 : ‖l‖ ^ 2 ≤ 1 := by
      rw [sq_le_one_iff₀ (norm_nonneg l)]; exact hl
    calc c * ‖l‖ ^ 2 ≤ c * 1 := mul_le_mul_of_nonneg_left hl2 hcpos.le
      _ = c := mul_one c
      _ ≤ χ l := h1
  · push Not at hl
    have hl0 : l ≠ 0 := by rintro rfl; rw [norm_zero] at hl; linarith
    have hinv : ‖l⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hl.le
    have h2 : c ≤ ρ l⁻¹ := (min_le_right _ _).trans (hmin₂ hinv)
    have hfac : l ^ 2 - t * l + n = l ^ 2 * (1 - t * l⁻¹ + n * l⁻¹ ^ 2) := by field_simp
    have hχl : χ l = ‖l‖ ^ 2 * ρ l⁻¹ := by
      show ‖l ^ 2 - t * l + n‖ = ‖l‖ ^ 2 * ‖1 - t * l⁻¹ + n * l⁻¹ ^ 2‖
      rw [hfac, norm_mul, norm_pow]
    have hl1 : 1 ≤ ‖l‖ ^ 2 := by nlinarith
    rw [hχl]
    constructor
    · calc c = 1 * c := (one_mul _).symm
        _ ≤ ‖l‖ ^ 2 * ρ l⁻¹ := mul_le_mul hl1 h2 hcpos.le (by positivity)
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)

include hreg hns in

theorem exists_forall_sq_le_mul_norm_det_lin :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : v.adicCompletion K,
      ‖x‖ ^ 2 ≤ C * ‖(lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y).det‖ ∧
      ‖y‖ ^ 2 ≤ C * ‖(lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y).det‖ := by
  obtain ⟨c, hc, hχ⟩ := exists_pos_forall_le_norm_charpoly K v γ₀ hreg hns
  refine ⟨max 1 c⁻¹, lt_max_of_lt_left one_pos, fun x y => ?_⟩
  set t := (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace with ht
  set n := (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det with hn
  have hQ0 : 0 ≤ ‖(lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y).det‖ := norm_nonneg _
  have conv : ∀ a : ℝ, c * a ≤ ‖(lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y).det‖ →
      a ≤ max 1 c⁻¹ * ‖(lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y).det‖ := by
    intro a h
    calc a ≤ ‖(lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x y).det‖ / c := (le_div_iff₀' hc).mpr h
      _ = c⁻¹ * _ := div_eq_inv_mul _ _
      _ ≤ max 1 c⁻¹ * _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hQ0
  by_cases hy : y = 0
  · subst hy
    have hdet : (lin (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) x 0).det = x ^ 2 := by rw [det_lin]; ring
    rw [hdet, norm_pow, norm_zero, zero_pow two_ne_zero]
    refine ⟨?_, by positivity⟩
    calc ‖x‖ ^ 2 = 1 * ‖x‖ ^ 2 := (one_mul _).symm
      _ ≤ max 1 c⁻¹ * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · refine ⟨conv _ ?_, conv _ ?_⟩ <;> rw [det_lin]
    · have hfac : x ^ 2 + t * x * y + n * y ^ 2 = y ^ 2 * ((-(x / y)) ^ 2 - t * (-(x / y)) + n) := by
        field_simp; ring
      rw [hfac, norm_mul, norm_pow]
      calc c * ‖x‖ ^ 2 = ‖y‖ ^ 2 * (c * ‖-(x / y)‖ ^ 2) := by
            rw [norm_neg, norm_div, div_pow]; field_simp
        _ ≤ ‖y‖ ^ 2 * ‖(-(x / y)) ^ 2 - t * -(x / y) + n‖ := mul_le_mul_of_nonneg_left (hχ _).2 (by positivity)
    · have hfac : x ^ 2 + t * x * y + n * y ^ 2 = y ^ 2 * ((-(x / y)) ^ 2 - t * (-(x / y)) + n) := by
        field_simp; ring
      rw [hfac, norm_mul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_left (hχ _).1 (by positivity)

end Local

end Ws31.Torus

end

namespace Ws31
namespace Torus

section TorusTrace

open AutomorphicForm Matrix

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
variable (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hreg : IsRegularSemisimple γ₀)
  (hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
    ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
       ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))

omit γ₀ in

theorem trace_mul_self_fin_two (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    (M * M).trace = M.trace ^ 2 - 2 * M.det := by
  rw [sq_eq_fin_two, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul, smul_eq_mul]
  push_cast
  ring

omit γ₀ in
theorem norm_two_le_one' : ‖(2 : v.adicCompletion K)‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff, ← HeightOneSpectrum.mem_adicCompletionIntegers]
  exact_mod_cast natCast_mem (v.adicCompletionIntegers K) 2

omit γ₀ in

theorem norm_sq_sub_two_mul (s d : v.adicCompletion K) (hs : 1 < ‖s‖) (hd : ‖d‖ ≤ 1) :
    ‖s ^ 2 - 2 * d‖ = ‖s‖ ^ 2 := by
  have h2d : ‖2 * d‖ < ‖s ^ 2‖ := by
    rw [norm_mul, norm_pow]
    calc ‖(2 : v.adicCompletion K)‖ * ‖d‖ ≤ 1 * 1 := mul_le_mul (norm_two_le_one' K v) hd (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
      _ < ‖s‖ ^ 2 := by nlinarith
  rw [← norm_pow]
  apply le_antisymm
  · calc ‖s ^ 2 - 2 * d‖ ≤ max ‖s ^ 2‖ ‖2 * d‖ := by
          rw [sub_eq_add_neg]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg])
      _ = ‖s ^ 2‖ := max_eq_left h2d.le
  · by_contra hlt
    push Not at hlt
    have : ‖s ^ 2‖ < ‖s ^ 2‖ :=
      calc ‖s ^ 2‖ = ‖(s ^ 2 - 2 * d) + 2 * d‖ := by rw [sub_add_cancel]
        _ ≤ max ‖s ^ 2 - 2 * d‖ ‖2 * d‖ := IsUltrametricDist.norm_add_le_max _ _
        _ < ‖s ^ 2‖ := max_lt hlt h2d
    exact lt_irrefl _ this

include hreg hns in

theorem norm_trace_le_one_of_norm_det_eq_one (m : GL (Fin 2) (v.adicCompletion K)) (hm : m ∈ localCentralizer K v γ₀)
    (hdet : ‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1) :
    ‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace‖ ≤ 1 := by
  obtain ⟨C, hC, hco⟩ := exists_forall_sq_le_mul_norm_det_lin K v γ₀ hreg hns
  set t := (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace with ht

  set R : ℝ := (1 + ‖t‖) * Real.sqrt C with hR
  have hbound : ∀ g : GL (Fin 2) (v.adicCompletion K), g ∈ localCentralizer K v γ₀ →
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 →
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace‖ ≤ R := by
    intro g hg hg1
    obtain ⟨x, y, hxy⟩ := (mem_localCentralizer_iff K v γ₀ hreg hns g).mp hg
    obtain ⟨hx2, hy2⟩ := hco x y
    rw [← hxy, hg1, mul_one] at hx2 hy2
    have hx : ‖x‖ ≤ Real.sqrt C := by rw [← Real.sqrt_sq (norm_nonneg x)]; exact Real.sqrt_le_sqrt hx2
    have hy : ‖y‖ ≤ Real.sqrt C := by rw [← Real.sqrt_sq (norm_nonneg y)]; exact Real.sqrt_le_sqrt hy2
    rw [hxy, trace_lin]
    calc ‖2 * x + t * y‖ ≤ ‖2 * x‖ + ‖t * y‖ := norm_add_le _ _
      _ = ‖(2 : v.adicCompletion K)‖ * ‖x‖ + ‖t‖ * ‖y‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * Real.sqrt C + ‖t‖ * Real.sqrt C :=
          add_le_add (mul_le_mul (norm_two_le_one' K v) hx (norm_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
      _ = R := by rw [hR]; ring

  by_contra hgt
  push Not at hgt
  set s := (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace with hs
  have hpow : ∀ k : ℕ, ‖((m ^ (2 ^ k) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace‖ =
      ‖s‖ ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => simp [hs]
    | succ k ih =>
      have hdetk : ‖((m ^ (2 ^ k) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ≤ 1 := by
        rw [Units.val_pow_eq_pow_val, Matrix.det_pow, norm_pow, hdet, one_pow]
      have hsk : 1 < ‖((m ^ (2 ^ k) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace‖ := by
        rw [ih]; exact one_lt_pow₀ hgt (pow_ne_zero k two_ne_zero)
      rw [pow_succ, pow_mul, pow_two, Units.val_mul, trace_mul_self_fin_two, norm_sq_sub_two_mul K v _ _ hsk hdetk, ih,
        ← pow_mul, ← pow_succ]

  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R hgt
  have hle : ‖s‖ ^ k ≤ ‖s‖ ^ (2 ^ k) :=
    pow_le_pow_right₀ hgt.le (Nat.lt_two_pow_self).le
  have hmk : m ^ (2 ^ k) ∈ localCentralizer K v γ₀ := Subgroup.pow_mem _ hm _
  have hdk : ‖((m ^ (2 ^ k) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 := by
    rw [Units.val_pow_eq_pow_val, Matrix.det_pow, norm_pow, hdet, one_pow]
  have := hbound _ hmk hdk
  rw [hpow] at this
  linarith

end TorusTrace

end Ws31.Torus

theorem solution
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (hγ₀e : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (m : GL (Fin 2) (v.adicCompletion K)) (hm : m ∈ AutomorphicForm.localCentralizer K v γ₀)
    (hdet : Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1) :
    Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1 := by
  have h1 : ‖((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det‖ = 1 :=
    le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr hdet.le) (Valued.toNormedField.one_le_norm_iff.mpr hdet.ge)
  exact Valued.toNormedField.norm_le_one_iff.mp
    (Ws31.Torus.norm_trace_le_one_of_norm_det_eq_one K v γ₀ hγ₀ hγ₀e m hm h1)

end S_AutomorphicForm_valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal
end P2MW
export P2MW.S_AutomorphicForm_valuation_trace_le_one_of_valuation_det_eq_one_of_mem_localCentralizer_of_forall_not_diagonal (solution)
