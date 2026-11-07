-- Prove2me | solution 1 for FiniteEnergyPlane.lt_of_mem_windingInterval_of_conj_of_loop
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T14:03:57.329206+00:00
-- url     : https://prove2.me/submissions/a3c9c6be-d95f-49bb-9f8d-e253d0ecc7cc

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Definitions.Def_HryniewiczCriterion_GraphAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.UnitInterval
import Theorems.Thm_FiniteEnergyPlane_exists_int_forall_mem_Ioo_of_forall_ne
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Theorems.Thm_HryniewiczCriterion_exists_polarAngleLift
import Mathlib

open HryniewiczCriterion
open HryniewiczCriterion Matrix
open scoped Real

namespace CZB2

noncomputable section

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

/-- `⟨e_s, M e_s⟩`. -/
def dotv (M : M2) (s : ℝ) : ℝ :=
  M 0 0 * Real.cos s ^ 2 + (M 0 1 + M 1 0) * Real.cos s * Real.sin s + M 1 1 * Real.sin s ^ 2

/-- `e_s × M e_s`. -/
def crossv (M : M2) (s : ℝ) : ℝ :=
  M 1 0 * Real.cos s ^ 2 + (M 1 1 - M 0 0) * Real.cos s * Real.sin s - M 0 1 * Real.sin s ^ 2

def zv (M : M2) (s : ℝ) : ℂ := (dotv M s : ℂ) + (crossv M s : ℂ) * Complex.I

@[simp] theorem zv_re (M : M2) (s : ℝ) : (zv M s).re = dotv M s := by simp [zv]
@[simp] theorem zv_im (M : M2) (s : ℝ) : (zv M s).im = crossv M s := by simp [zv]

theorem mulVec_rv (M : M2) (s : ℝ) :
    M *ᵥ rotationVector s = ![dotv M s * Real.cos s - crossv M s * Real.sin s,
      dotv M s * Real.sin s + crossv M s * Real.cos s] := by
  have h := Real.sin_sq_add_cos_sq s
  ext i; fin_cases i <;>
    simp [rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two, dotv, crossv]
  · linear_combination (-(M 0 0 * Real.cos s) - M 0 1 * Real.sin s) * h
  · linear_combination (-(M 1 0 * Real.cos s) - M 1 1 * Real.sin s) * h

theorem dotProduct_eq (M : M2) (s : ℝ) :
    rotationVector s ⬝ᵥ (M *ᵥ rotationVector s) = dotv M s := by
  have h := Real.sin_sq_add_cos_sq s
  rw [mulVec_rv]
  simp [rotationVector, dotProduct, Fin.sum_univ_two]
  linear_combination dotv M s * h

theorem mulVec_eq_smul (M : M2) (s : ℝ) :
    M *ᵥ rotationVector s = ‖zv M s‖ • rotationVector (s + Complex.arg (zv M s)) := by
  have hc := Complex.norm_mul_cos_arg (zv M s)
  have hs := Complex.norm_mul_sin_arg (zv M s)
  simp only [zv_re, zv_im] at hc hs
  rw [mulVec_rv]
  ext i; fin_cases i <;> simp [rotationVector, Real.cos_add, Real.sin_add]
  · rw [← hc, ← hs]; ring
  · rw [← hc, ← hs]; ring

theorem rot_mulVec (a x : ℝ) : rotationMatrix a *ᵥ rotationVector x = rotationVector (a + x) := by
  ext i; fin_cases i <;>
    simp [rotationMatrix, rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Real.cos_add, Real.sin_add] <;> ring

theorem rot_mul_apply0 (a : ℝ) (M : M2) (j : Fin 2) :
    (rotationMatrix a * M) 0 j = Real.cos a * M 0 j - Real.sin a * M 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [rotationMatrix]; ring

theorem rot_mul_apply1 (a : ℝ) (M : M2) (j : Fin 2) :
    (rotationMatrix a * M) 1 j = Real.sin a * M 0 j + Real.cos a * M 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [rotationMatrix]

theorem rot_neg_mul (a : ℝ) : rotationMatrix (-a) * rotationMatrix a = 1 := by
  have h := Real.sin_sq_add_cos_sq a
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

theorem rv_ne_zero (s : ℝ) : rotationVector s ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [rotationVector] at h0 h1
  have := Real.sin_sq_add_cos_sq s
  rw [h0, h1] at this; norm_num at this

theorem cos_sub_eq_one {r r' x y : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (h : r' • rotationVector x = r • rotationVector y) : Real.cos (x - y) = 1 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [rotationVector] at h0 h1
  have hx := Real.sin_sq_add_cos_sq x
  have hy := Real.sin_sq_add_cos_sq y
  have hsq : r' ^ 2 = r ^ 2 := by
    have : (r' * Real.sin x) ^ 2 + (r' * Real.cos x) ^ 2 = (r * Real.sin y) ^ 2 + (r * Real.cos y) ^ 2 := by
      rw [h0, h1]
    nlinarith
  have hrr : r' = r := by nlinarith
  subst hrr
  have hc : Real.cos x = Real.cos y := mul_left_cancel₀ hr.ne' h0
  have hs : Real.sin x = Real.sin y := mul_left_cancel₀ hr.ne' h1
  rw [Real.cos_sub, hc, hs]; linarith

theorem polar (x y : ℝ) (h : x ≠ 0 ∨ y ≠ 0) :
    ∃ s ∈ Set.Icc 0 (2 * Real.pi), ∃ ρ : ℝ, 0 < ρ ∧ x = ρ * Real.cos s ∧ y = ρ * Real.sin s := by
  set z : ℂ := ⟨x, y⟩
  have hz : z ≠ 0 := by
    intro e; rcases h with h | h
    · exact h (congrArg Complex.re e)
    · exact h (congrArg Complex.im e)
  have hc := Complex.norm_mul_cos_arg z
  have hs := Complex.norm_mul_sin_arg z
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  have hpi := Real.pi_pos
  by_cases ha : 0 ≤ Complex.arg z
  · exact ⟨Complex.arg z, ⟨ha, by linarith⟩, ‖z‖, hpos, hc.symm, hs.symm⟩
  · refine ⟨Complex.arg z + 2 * Real.pi, ⟨by linarith, by linarith⟩, ‖z‖, hpos, ?_, ?_⟩
    · rw [Real.cos_add_two_pi]; exact hc.symm
    · rw [Real.sin_add_two_pi]; exact hs.symm

theorem indef (c m b : ℝ) (h : 0 < m ^ 2 + 4 * b * c) :
    ∃ x y : ℝ, 0 < c * x ^ 2 + m * x * y - b * y ^ 2 := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · exact ⟨0, 1, by nlinarith⟩
  · subst hb
    have hm : m ≠ 0 := by intro e; subst e; norm_num at h
    refine ⟨m / (2 * |c| + 1), 1, ?_⟩
    have hd : 0 < 2 * |c| + 1 := by positivity
    have hm2 : 0 < m ^ 2 := by positivity
    have e : c * (m / (2 * |c| + 1)) ^ 2 + m * (m / (2 * |c| + 1)) * 1 - 0 * 1 ^ 2 =
        m ^ 2 * (c + (2 * |c| + 1)) / (2 * |c| + 1) ^ 2 := by field_simp; ring
    rw [e]
    apply div_pos _ (by positivity)
    apply mul_pos hm2
    have := neg_abs_le c
    linarith
  · exact ⟨2 * b, m, by nlinarith⟩

/-- `e_s × B e_s = r sin(θ - s)` when `B e_s = r e_θ`. -/
theorem crossv_eq (B : M2) (s r θ : ℝ) (h : B *ᵥ rotationVector s = r • rotationVector θ) :
    crossv B s = r * Real.sin (θ - s) := by
  have hc := Real.sin_sq_add_cos_sq s
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [mulVec_rv] at h0 h1
  simp [rotationVector] at h0 h1
  rw [Real.sin_sub]
  linear_combination (-crossv B s) * hc + Real.cos s * h1 - Real.sin s * h0

/-- `crossv` at a nonzero vector, scaled. -/
theorem crossv_polar (B : M2) (ρ s : ℝ) :
    B 1 0 * (ρ * Real.cos s) ^ 2 + (B 1 1 - B 0 0) * (ρ * Real.cos s) * (ρ * Real.sin s) -
      B 0 1 * (ρ * Real.sin s) ^ 2 = ρ ^ 2 * crossv B s := by
  simp only [crossv]; ring

end

end CZB2

namespace HryniewiczCriterion

theorem lw_cos_sub_eq_one {r r' x y : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (h : r' • rotationVector x = r • rotationVector y) : Real.cos (x - y) = 1 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [rotationVector] at h0 h1
  have hx := Real.sin_sq_add_cos_sq x
  have hy := Real.sin_sq_add_cos_sq y
  have hsq : r' ^ 2 = r ^ 2 := by
    have : (r' * Real.sin x) ^ 2 + (r' * Real.cos x) ^ 2 =
        (r * Real.sin y) ^ 2 + (r * Real.cos y) ^ 2 := by
      rw [h0, h1]
    nlinarith
  have hrr : r' = r := by nlinarith
  subst hrr
  have hc : Real.cos x = Real.cos y := mul_left_cancel₀ hr.ne' h0
  have hs : Real.sin x = Real.sin y := mul_left_cancel₀ hr.ne' h1
  rw [Real.cos_sub, hc, hs]; linarith

theorem lw_int_eq_of_lt {z a : ℤ} (h1 : (a : ℝ) - 1 < z) (h2 : (z : ℝ) < a + 1) : z = a := by
  have h1' : a - 1 < z := by exact_mod_cast h1
  have h2' : z < a + 1 := by exact_mod_cast h2
  omega

/-- Two angle lifts with the same starting angle agree at `t = 1`. -/
theorem lw_isAngleLift_eq_one {φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {s : ℝ} {θ θ' : ℝ → ℝ}
    (hθ : IsAngleLift φ s θ) (hθ' : IsAngleLift φ s θ') : θ' 1 = θ 1 := by
  have hpi := Real.pi_pos
  let f : unitInterval → ℝ := fun t => θ' t - θ t
  have hfc : Continuous f :=
    (hθ'.1.comp_continuous continuous_subtype_val (fun t => t.2)).sub
      (hθ.1.comp_continuous continuous_subtype_val (fun t => t.2))
  have hcos : ∀ t : unitInterval, Real.cos (f t) = 1 := by
    intro t
    obtain ⟨r', hr', e'⟩ := hθ'.2.2 t t.2
    obtain ⟨r, hr, e⟩ := hθ.2.2 t t.2
    exact lw_cos_sub_eq_one hr hr' (e'.symm.trans e)
  obtain ⟨m, hm⟩ := FiniteEnergyPlane.exists_int_forall_mem_Ioo_of_forall_ne f hfc Real.pi
    (2 * Real.pi) (by linarith) (by
      intro t m e
      have := hcos t
      rw [e, Real.cos_add_int_mul_two_pi, Real.cos_pi] at this
      norm_num at this)
  have hf0 : f 0 = 0 := by
    simp only [f, Set.Icc.coe_zero, hθ.2.1, hθ'.2.1, sub_self]
  have hm1 : m = -1 := by
    obtain ⟨a1, a2⟩ := hm 0
    rw [hf0] at a1 a2
    apply lw_int_eq_of_lt <;> push_cast <;> nlinarith
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (f 1)).1 (hcos 1)
  have hn0 : n = 0 := by
    obtain ⟨a1, a2⟩ := hm 1
    rw [← hn, hm1] at a1 a2
    push_cast at a1 a2
    apply lw_int_eq_of_lt <;> push_cast <;> nlinarith
  have : f 1 = 0 := by rw [← hn, hn0]; simp
  simpa [f, sub_eq_zero] using this

/-- If `θ s` is an angle lift of `φ` starting at `s` for every `s`, then the winding interval of
`φ` is the image of `s ↦ (θ s 1 - s) / 2π` on `[0, 2π]`. -/
theorem windingInterval_eq_image_of_isAngleLift_aux (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (θ : ℝ → ℝ → ℝ) (hθ : ∀ s, IsAngleLift φ s (θ s)) :
    windingInterval φ =
      (fun s => (θ s 1 - s) / (2 * Real.pi)) '' Set.Icc 0 (2 * Real.pi) := by
  ext d
  constructor
  · rintro ⟨s, hs, θ', hθ', rfl⟩
    exact ⟨s, hs, by simp only [lw_isAngleLift_eq_one (hθ s) hθ']⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, θ s, hθ s, rfl⟩

end HryniewiczCriterion

namespace FiniteEnergyPlane

open CZB2

noncomputable section

/-- The angle `γ ↦ γ + c + arg ⟨e, R(-c) M e⟩ + i (e × R(-c) M e)`. -/
def fwAngle (M : M2) (c γ : ℝ) : ℝ := γ + c + Complex.arg (zv (rotationMatrix (-c) * M) γ)

theorem fw_rot_cancel (c : ℝ) (M : M2) : rotationMatrix c * (rotationMatrix (-c) * M) = M := by
  have h : rotationMatrix c * rotationMatrix (-c) = 1 := by
    have := rot_neg_mul (-c)
    rwa [neg_neg] at this
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

/-- `M e^{iγ}` has the direction `fwAngle`. -/
theorem fw_mulVec (M : M2) (c γ : ℝ) :
    M *ᵥ rotationVector γ =
      ‖zv (rotationMatrix (-c) * M) γ‖ • rotationVector (fwAngle M c γ) := by
  conv_lhs => rw [← fw_rot_cancel c M, ← Matrix.mulVec_mulVec, mulVec_eq_smul,
    Matrix.mulVec_smul, rot_mulVec]
  unfold fwAngle
  congr 2
  ring

theorem fw_zv_ne {M : M2} {c γ : ℝ} (h : 0 < dotv (rotationMatrix (-c) * M) γ) :
    0 < ‖zv (rotationMatrix (-c) * M) γ‖ := by
  apply norm_pos_iff.2
  intro h0
  have := congrArg Complex.re h0
  simp at this
  linarith

theorem fw_rv_periodic (γ : ℝ) : rotationVector (γ + 2 * π) = rotationVector γ := by
  funext i
  fin_cases i <;> simp [rotationVector]

theorem fw_rv_sub_int (γ : ℝ) (n : ℤ) : rotationVector (γ - n * (2 * π)) = rotationVector γ := by
  funext i
  fin_cases i <;> simp [rotationVector, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]

theorem fw_dotv_add (M : M2) (γ : ℝ) : dotv M (γ + 2 * π) = dotv M γ := by
  simp [dotv]

theorem fw_zv_add (M : M2) (γ : ℝ) : zv M (γ + 2 * π) = zv M γ := by
  simp [zv, dotv, crossv]

theorem fw_angle_add (M : M2) (c γ : ℝ) :
    fwAngle M c (γ + 2 * π) = fwAngle M c γ + 2 * π := by
  unfold fwAngle
  rw [fw_zv_add]
  ring

theorem fw_angle_add_int (M : M2) (c γ : ℝ) (n : ℤ) :
    fwAngle M c (γ + n * (2 * π)) = fwAngle M c γ + n * (2 * π) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    push_cast at ih ⊢
    rw [show γ + ((i : ℝ) + 1) * (2 * π) = γ + (i : ℝ) * (2 * π) + 2 * π by ring, fw_angle_add, ih]
    ring
  | pred i ih =>
    push_cast at ih ⊢
    have := fw_angle_add M c (γ + (-(i : ℝ) - 1) * (2 * π))
    rw [show γ + (-(i : ℝ) - 1) * (2 * π) + 2 * π = γ + -(i : ℝ) * (2 * π) by ring, ih] at this
    linarith

/-- Continuity of the angle along continuous data, where the real part stays positive. -/
theorem fw_continuousOn_angle (M : ℝ → M2) (c γ : ℝ → ℝ) (K : Set ℝ)
    (hM : ∀ i j, ContinuousOn (fun t => M t i j) K) (hc : ContinuousOn c K)
    (hγ : ContinuousOn γ K)
    (hpos : ∀ t ∈ K, 0 < dotv (rotationMatrix (-c t) * M t) (γ t)) :
    ContinuousOn (fun t => fwAngle (M t) (c t) (γ t)) K := by
  have hC : ContinuousOn (fun t => Real.cos (-c t)) K := Real.continuous_cos.comp_continuousOn hc.neg
  have hS : ContinuousOn (fun t => Real.sin (-c t)) K := Real.continuous_sin.comp_continuousOn hc.neg
  have hE0 : ∀ j, ContinuousOn (fun t => (rotationMatrix (-c t) * M t) 0 j) K := by
    intro j
    simp only [rot_mul_apply0]
    exact (hC.mul (hM 0 j)).sub (hS.mul (hM 1 j))
  have hE1 : ∀ j, ContinuousOn (fun t => (rotationMatrix (-c t) * M t) 1 j) K := by
    intro j
    simp only [rot_mul_apply1]
    exact (hS.mul (hM 0 j)).add (hC.mul (hM 1 j))
  have hcγ : ContinuousOn (fun t => Real.cos (γ t)) K := Real.continuous_cos.comp_continuousOn hγ
  have hsγ : ContinuousOn (fun t => Real.sin (γ t)) K := Real.continuous_sin.comp_continuousOn hγ
  have hd : ContinuousOn (fun t => dotv (rotationMatrix (-c t) * M t) (γ t)) K := by
    unfold dotv
    exact (((hE0 0).mul (hcγ.pow 2)).add ((((hE0 1).add (hE1 0)).mul hcγ).mul hsγ)).add
      ((hE1 1).mul (hsγ.pow 2))
  have hx : ContinuousOn (fun t => crossv (rotationMatrix (-c t) * M t) (γ t)) K := by
    unfold crossv
    exact (((hE1 0).mul (hcγ.pow 2)).add ((((hE1 1).sub (hE0 0)).mul hcγ).mul hsγ)).sub
      ((hE0 1).mul (hsγ.pow 2))
  have hz : ContinuousOn (fun t => zv (rotationMatrix (-c t) * M t) (γ t)) K := by
    unfold zv
    exact (Complex.continuous_ofReal.comp_continuousOn hd).add
      ((Complex.continuous_ofReal.comp_continuousOn hx).mul continuousOn_const)
  have harg : ContinuousOn (fun t => Complex.arg (zv (rotationMatrix (-c t) * M t) (γ t))) K := by
    intro t ht
    have hslit : zv (rotationMatrix (-c t) * M t) (γ t) ∈ Complex.slitPlane :=
      Or.inl (by simpa using hpos t ht)
    exact ContinuousWithinAt.comp (g := Complex.arg)
      (f := fun t => zv (rotationMatrix (-c t) * M t) (γ t)) (t := Set.univ)
      (Complex.continuousAt_arg hslit).continuousWithinAt (hz t ht) (Set.mapsTo_univ _ _)
  unfold fwAngle
  exact (hγ.add hc).add harg

/-- For determinant one, the rotation part `c = arg (tr M + i (M₁₀ - M₀₁))` makes the form positive. -/
theorem fw_exists_rot (M : M2) (hdet : M.det = 1) :
    ∃ c : ℝ, ∀ γ, 0 < dotv (rotationMatrix (-c) * M) γ := by
  set a := M 0 0
  set b := M 0 1
  set c' := M 1 0
  set d := M 1 1
  have hd : a * d - b * c' = 1 := by
    rw [Matrix.det_fin_two] at hdet
    exact hdet
  set w : ℂ := ⟨a + d, c' - b⟩ with hw
  have hw0 : w ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [hw] at h1 h2
    nlinarith [sq_nonneg (a - d), sq_nonneg (b + c')]
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  refine ⟨Complex.arg w, fun γ => ?_⟩
  have hC : ‖w‖ * Real.cos (Complex.arg w) = a + d := by
    simpa [hw] using Complex.norm_mul_cos_arg w
  have hS : ‖w‖ * Real.sin (Complex.arg w) = c' - b := by
    simpa [hw] using Complex.norm_mul_sin_arg w
  set C := Real.cos (Complex.arg w)
  set S := Real.sin (Complex.arg w)
  have hCS : C ^ 2 + S ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have e00 : (rotationMatrix (-Complex.arg w) * M) 0 0 = C * a + S * c' := by
    rw [rot_mul_apply0, Real.cos_neg, Real.sin_neg]; ring
  have e01 : (rotationMatrix (-Complex.arg w) * M) 0 1 = C * b + S * d := by
    rw [rot_mul_apply0, Real.cos_neg, Real.sin_neg]; ring
  have e10 : (rotationMatrix (-Complex.arg w) * M) 1 0 = -S * a + C * c' := by
    rw [rot_mul_apply1, Real.cos_neg, Real.sin_neg]
  have e11 : (rotationMatrix (-Complex.arg w) * M) 1 1 = -S * b + C * d := by
    rw [rot_mul_apply1, Real.cos_neg, Real.sin_neg]
  set p := C * a + S * c'
  set q := C * b + S * d
  set q' := -S * a + C * c'
  set r := -S * b + C * d
  -- the rotated matrix is symmetric of positive trace and determinant one
  have hsym : q = q' := by
    have : ‖w‖ * (q - q') = 0 := by
      have : ‖w‖ * (q - q') = (‖w‖ * C) * (b - c') + (‖w‖ * S) * (a + d) := by
        simp only [q, q']; ring
      rw [this, hC, hS]; ring
    have := (mul_eq_zero.1 this).resolve_left hn.ne'
    linarith
  have htr : p + r = ‖w‖ := by
    have : ‖w‖ * (p + r) = ‖w‖ * ‖w‖ := by
      have e : ‖w‖ * (p + r) = (‖w‖ * C) * (a + d) + (‖w‖ * S) * (c' - b) := by
        simp only [p, r]; ring
      rw [e, hC, hS]
      have : ‖w‖ * ‖w‖ = (‖w‖ * C) ^ 2 + (‖w‖ * S) ^ 2 := by
        have : (‖w‖ * C) ^ 2 + (‖w‖ * S) ^ 2 = ‖w‖ ^ 2 * (C ^ 2 + S ^ 2) := by ring
        rw [this, hCS]; ring
      rw [this, hC, hS]; ring
    exact mul_left_cancel₀ hn.ne' this
  have hdetP : p * r - q * q' = 1 := by
    have e : p * r - q * q' = (C ^ 2 + S ^ 2) * (a * d - b * c') := by
      simp only [p, q, q', r]; ring
    rw [e, hCS, hd]; ring
  have hpr : 0 < p * r := by
    have e : q * q' = q ^ 2 := by rw [← hsym]; ring
    nlinarith [sq_nonneg q]
  have hp : 0 < p := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpr with h | h
    · exact h.1
    · linarith [h.1, h.2]
  have hr : 0 < r := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpr with h | h
    · exact h.2
    · linarith [h.1, h.2]
  unfold dotv
  rw [e00, e01, e10, e11, ← hsym]
  set x := Real.cos γ
  set y := Real.sin γ
  have hxy : x ^ 2 + y ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hqq : p * r - q ^ 2 = 1 := by rw [← hdetP, hsym]; ring
  have key : p * (p * x ^ 2 + (q + q) * x * y + r * y ^ 2) = (p * x + q * y) ^ 2 + y ^ 2 := by
    linear_combination y ^ 2 * hqq
  have : 0 < p * (p * x ^ 2 + (q + q) * x * y + r * y ^ 2) := by
    rw [key]
    by_cases hy : y = 0
    · have hx : x ^ 2 = 1 := by rw [hy] at hxy; linarith
      rw [hy]
      have : p * x = p * x := rfl
      have hpx : (p * x) ^ 2 = p ^ 2 := by rw [mul_pow, hx, mul_one]
      nlinarith [sq_pos_of_pos hp]
    · have := sq_pos_of_ne_zero hy
      nlinarith [sq_nonneg (p * x + q * y)]
  exact (pos_iff_pos_of_mul_pos this).1 hp

/-- `γ ↦ fwAngle M c γ` is strictly increasing for determinant one. -/
theorem fw_strictMono_angle (M : M2) (hdet : M.det = 1) (c : ℝ)
    (hpos : ∀ γ, 0 < dotv (rotationMatrix (-c) * M) γ) : StrictMono (fwAngle M c) := by
  have hcont : Continuous (fwAngle M c) := by
    rw [← continuousOn_univ]
    exact fw_continuousOn_angle (fun _ => M) (fun _ => c) (fun t => t) Set.univ
      (fun _ _ => continuousOn_const) continuousOn_const continuousOn_id (fun t _ => hpos t)
  have hinj : Function.Injective (fwAngle M c) := by
    intro x y hxy
    have h1 := fw_mulVec M c x
    have h2 := fw_mulVec M c y
    rw [hxy] at h1
    have hu : IsUnit M.det := by rw [hdet]; exact isUnit_one
    set a := ‖zv (rotationMatrix (-c) * M) x‖
    set b := ‖zv (rotationMatrix (-c) * M) y‖
    have ha : 0 < a := fw_zv_ne (hpos x)
    have hb : 0 < b := fw_zv_ne (hpos y)
    have hrv : rotationVector x = (a / b) • rotationVector y := by
      have e : M *ᵥ rotationVector x = M *ᵥ ((a / b) • rotationVector y) := by
        rw [h1, Matrix.mulVec_smul, h2, smul_smul, div_mul_cancel₀ _ hb.ne']
      calc rotationVector x = M⁻¹ *ᵥ (M *ᵥ rotationVector x) := by
            rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
        _ = M⁻¹ *ᵥ (M *ᵥ ((a / b) • rotationVector y)) := by rw [e]
        _ = (a / b) • rotationVector y := by
            rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    have hcos : Real.cos (x - y) = 1 := by
      have : (1 : ℝ) • rotationVector x = (a / b) • rotationVector y := by
        rw [one_smul]; exact hrv
      exact cos_sub_eq_one (div_pos ha hb) one_pos this
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (x - y)).1 hcos
    have hxe : x = y + n * (2 * π) := by linarith
    have h3 : fwAngle M c x = fwAngle M c y + n * (2 * π) := by
      rw [hxe, fw_angle_add_int]
    have hn0 : (n : ℝ) * (2 * π) = 0 := by linarith
    rw [hxe, hn0, add_zero]
  rcases hcont.strictMono_of_inj hinj with h | h
  · exact h
  · have := h (show (0 : ℝ) < 0 + 2 * π by positivity)
    rw [fw_angle_add] at this
    have hp := Real.pi_pos
    linarith

theorem fw_angle_one (γ : ℝ) : fwAngle (1 : M2) 0 γ = γ := by
  have hR : rotationMatrix (-(0 : ℝ)) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotationMatrix]
  have hz : zv (rotationMatrix (-(0 : ℝ)) * (1 : M2)) γ = 1 := by
    rw [hR, Matrix.one_mul]
    apply Complex.ext
    · simp [dotv]
    · simp [crossv]
  unfold fwAngle
  rw [hz, Complex.arg_one]
  ring

theorem fw_det_inv (A : M2) (hA : A.det = 1) : (A⁻¹).det = 1 := by
  have hu : IsUnit A.det := by rw [hA]; exact isUnit_one
  have := Matrix.det_mul A⁻¹ A
  rw [Matrix.nonsing_inv_mul _ hu, Matrix.det_one, hA, mul_one] at this
  exact this.symm

/-- A winding threshold passes from `t ↦ G(t) φ(t) G(0)⁻¹` to `φ`, for a loop `G` in `SL(2, ℝ)` such
that `t ↦ G(t) G(0)⁻¹ e₁` has winding number zero. No condition on `φ(1)` is imposed. -/
theorem lt_of_mem_windingInterval_of_conj_of_loop_aux (φ G : ℝ → M2)
    (hGc : ContinuousOn G (Set.Icc 0 1)) (hGd : ∀ t ∈ Set.Icc (0 : ℝ) 1, (G t).det = 1)
    (hG1 : G 1 = G 0) (θ : ℝ → ℝ) (hθc : ContinuousOn θ (Set.Icc 0 1)) (hθ1 : θ 1 = θ 0)
    (hθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧
      (G t * (G 0)⁻¹).mulVec (rotationVector 0) = r • rotationVector (θ t)) (k : ℤ)
    (h : ∀ d ∈ windingInterval (fun t => G t * φ t * (G 0)⁻¹), (k : ℝ) < d) :
    ∀ d ∈ windingInterval φ, (k : ℝ) < d := by
  have hpi := Real.pi_pos
  rintro d ⟨s₀, -, β, hβ, rfl⟩
  have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have h1m : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have hdet0 : (G 0).det = 1 := hGd 0 h0m
  have hu0 : IsUnit (G 0).det := by rw [hdet0]; exact isUnit_one
  set Gt : ℝ → M2 := fun t => G t * (G 0)⁻¹ with hGt
  have hGtc : ContinuousOn Gt (Set.Icc 0 1) := hGc.mul continuousOn_const
  have hGte : ∀ i j, ContinuousOn (fun t => Gt t i j) (Set.Icc 0 1) := fun i j =>
    (continuous_id.matrix_elem i j).comp_continuousOn hGtc
  have hGtd : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Gt t).det = 1 := fun t ht => by
    simp only [hGt]
    rw [Matrix.det_mul, hGd t ht, fw_det_inv _ hdet0, one_mul]
  have hGt0 : Gt 0 = 1 := Matrix.mul_nonsing_inv _ hu0
  have hGt1 : Gt 1 = 1 := by simp only [hGt]; rw [hG1]; exact hGt0
  have hGG : ∀ t, G t = Gt t * G 0 := fun t => by
    simp only [hGt]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu0, Matrix.mul_one]
  -- the polar rotation angle of `Gt`
  obtain ⟨α, hαc, hα0, hαP⟩ := exists_polarAngleLift Gt
    (continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hGte i j) hGtd hGt0
  have hαpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ γ, 0 < dotv (rotationMatrix (-α t) * Gt t) γ := by
    intro t ht γ
    obtain ⟨P, hP, e⟩ := hαP t ht
    rw [e, ← Matrix.mul_assoc, rot_neg_mul, Matrix.one_mul, ← dotProduct_eq]
    simpa using hP.dotProduct_mulVec_pos (rv_ne_zero γ)
  -- `α 1 = 0`
  have hα1 : α 1 = 0 := by
    obtain ⟨P, hP, e⟩ := hαP 1 h1m
    rw [hGt1] at e
    have hPe : P = rotationMatrix (-α 1) := by
      have := congrArg (fun A => rotationMatrix (-α 1) * A) e
      rw [Matrix.mul_one, ← Matrix.mul_assoc, rot_neg_mul, Matrix.one_mul] at this
      exact this.symm
    have hsym := congrFun (congrFun hP.isHermitian 0) 1
    rw [hPe] at hsym
    simp [rotationMatrix, Matrix.conjTranspose_apply] at hsym
    have hsin : Real.sin (α 1) = 0 := by linarith
    have hcos : 0 < Real.cos (α 1) := by
      have := hαpos 1 h1m 0
      rw [hGt1, Matrix.mul_one] at this
      simpa [dotv, rotationMatrix] using this
    -- compare with the given lift of winding zero
    obtain ⟨r₀, hr₀, e₀⟩ := hθ 0 h0m
    have hG0v : Gt 0 *ᵥ rotationVector 0 = rotationVector 0 := by
      rw [hGt0, Matrix.one_mulVec]
    have hcos0 : Real.cos (θ 0 - 0) = 1 := by
      apply cos_sub_eq_one one_pos hr₀
      rw [one_smul, ← e₀]
      exact hG0v
    obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).1 hcos0
    have hm' : θ 0 = m * (2 * π) := by linarith
    have hL1 : IsAngleLift Gt 0 (fun t => θ t - m * (2 * π)) := by
      refine ⟨hθc.sub continuousOn_const, by simp only; rw [hm']; ring, fun t ht => ?_⟩
      obtain ⟨r, hr, e⟩ := hθ t ht
      refine ⟨r, hr, ?_⟩
      rw [fw_rv_sub_int]
      exact e
    have hL2 : IsAngleLift Gt 0 (fun t => fwAngle (Gt t) (α t) 0) := by
      refine ⟨fw_continuousOn_angle Gt α (fun _ => 0) _ hGte hαc continuousOn_const
        (fun t ht => hαpos t ht 0), ?_, fun t ht => ?_⟩
      · simp only
        rw [hGt0, hα0, fw_angle_one]
      · exact ⟨_, fw_zv_ne (hαpos t ht 0), fw_mulVec (Gt t) (α t) 0⟩
    have heq : fwAngle (Gt 1) (α 1) 0 = θ 1 - m * (2 * π) := lw_isAngleLift_eq_one hL1 hL2
    rw [hGt1, hθ1, hm', sub_self] at heq
    have hzv : zv (rotationMatrix (-α 1) * (1 : M2)) 0 = (Real.cos (α 1) : ℝ) := by
      rw [Matrix.mul_one]
      apply Complex.ext
      · rw [zv_re, Complex.ofReal_re]
        simp [dotv, rotationMatrix]
      · rw [zv_im, Complex.ofReal_im]
        simp [crossv, rotationMatrix, hsin]
    unfold fwAngle at heq
    rw [hzv, Complex.arg_ofReal_of_nonneg hcos.le] at heq
    linarith
  -- the direction map of the constant matrix `G 0`
  obtain ⟨c₀, hc₀⟩ := fw_exists_rot (G 0) hdet0
  set g := fwAngle (G 0) c₀ with hg
  have hgm : StrictMono g := fw_strictMono_angle (G 0) hdet0 c₀ hc₀
  have hgc : Continuous g := by
    rw [← continuousOn_univ]
    exact fw_continuousOn_angle (fun _ => G 0) (fun _ => c₀) (fun t => t) Set.univ
      (fun _ _ => continuousOn_const) continuousOn_const continuousOn_id (fun t _ => hc₀ t)
  set s := g s₀ with hs
  set ρ := ‖zv (rotationMatrix (-c₀) * G 0) s₀‖ with hρ
  have hρ0 : 0 < ρ := fw_zv_ne (hc₀ s₀)
  have hG0s : G 0 *ᵥ rotationVector s₀ = ρ • rotationVector s := fw_mulVec (G 0) c₀ s₀
  have hinv : (G 0)⁻¹ *ᵥ rotationVector s = ρ⁻¹ • rotationVector s₀ := by
    have e : rotationVector s₀ = ρ • ((G 0)⁻¹ *ᵥ rotationVector s) := by
      calc rotationVector s₀ = (G 0)⁻¹ *ᵥ (G 0 *ᵥ rotationVector s₀) := by
            rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu0, Matrix.one_mulVec]
        _ = _ := by rw [hG0s, Matrix.mulVec_smul]
    rw [e, smul_smul, inv_mul_cancel₀ hρ0.ne', one_smul]
  -- the lift of the conjugated path
  set θF : ℝ → ℝ := fun t => fwAngle (Gt t) (α t) (g (β t)) with hθF
  have hθF0 : θF 0 = s := by
    simp only [hθF]
    rw [hGt0, hα0, fw_angle_one, hβ.2.1]
  have hθF1 : θF 1 = g (β 1) := by
    simp only [hθF]
    rw [hGt1, hα1, fw_angle_one]
  have hF : IsAngleLift (fun t => G t * φ t * (G 0)⁻¹) s θF := by
    refine ⟨fw_continuousOn_angle Gt α (fun t => g (β t)) _ hGte hαc
      (hgc.comp_continuousOn hβ.1) (fun t ht => hαpos t ht _), hθF0, fun t ht => ?_⟩
    obtain ⟨r, hr, e⟩ := hβ.2.2 t ht
    refine ⟨ρ⁻¹ * r * ‖zv (rotationMatrix (-c₀) * G 0) (β t)‖ *
      ‖zv (rotationMatrix (-α t) * Gt t) (g (β t))‖,
      mul_pos (mul_pos (mul_pos (inv_pos.2 hρ0) hr) (fw_zv_ne (hc₀ _))) (fw_zv_ne (hαpos t ht _)), ?_⟩
    have hb : G 0 *ᵥ rotationVector (β t) =
        ‖zv (rotationMatrix (-c₀) * G 0) (β t)‖ • rotationVector (g (β t)) :=
      fw_mulVec (G 0) c₀ (β t)
    have hc : Gt t *ᵥ rotationVector (g (β t)) =
        ‖zv (rotationMatrix (-α t) * Gt t) (g (β t))‖ • rotationVector (θF t) :=
      fw_mulVec (Gt t) (α t) (g (β t))
    calc (G t * φ t * (G 0)⁻¹) *ᵥ rotationVector s
        = Gt t *ᵥ (G 0 *ᵥ (φ t *ᵥ ((G 0)⁻¹ *ᵥ rotationVector s))) := by
          rw [hGG t]
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = _ := by
          rw [hinv]
          simp only [Matrix.mulVec_smul, e, hb, hc, smul_smul]
  -- normalize the starting angle
  set n : ℤ := ⌊s / (2 * π)⌋ with hn
  have hs1 : 0 ≤ s - n * (2 * π) := by
    have h1 := Int.floor_le (s / (2 * π))
    have h2 : (n : ℝ) * (2 * π) ≤ s / (2 * π) * (2 * π) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at h2
    linarith
  have hs2 : s - n * (2 * π) ≤ 2 * π := by
    have h1 := Int.lt_floor_add_one (s / (2 * π))
    have h2 : s / (2 * π) * (2 * π) ≤ ((n : ℝ) + 1) * (2 * π) :=
      mul_le_mul_of_nonneg_right h1.le (by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at h2
    linarith
  have hF' : IsAngleLift (fun t => G t * φ t * (G 0)⁻¹) (s - n * (2 * π))
      (fun t => θF t - n * (2 * π)) := by
    refine ⟨hF.1.sub continuousOn_const, by simp only; rw [hθF0], fun t ht => ?_⟩
    obtain ⟨r, hr, e⟩ := hF.2.2 t ht
    refine ⟨r, hr, ?_⟩
    rw [fw_rv_sub_int, fw_rv_sub_int]
    exact e
  have hd : (k : ℝ) < (θF 1 - n * (2 * π) - (s - n * (2 * π))) / (2 * π) :=
    h _ ⟨_, ⟨hs1, hs2⟩, _, hF', rfl⟩
  have hd2 : (k : ℝ) * (2 * π) < g (β 1) - g s₀ := by
    rw [lt_div_iff₀ (by positivity), hθF1] at hd
    have e : g (β 1) - n * (2 * π) - (s - n * (2 * π)) = g (β 1) - g s₀ := by rw [hs]; ring
    rw [e] at hd
    exact hd
  have hg1 : g (s₀ + k * (2 * π)) < g (β 1) := by
    have : g (s₀ + k * (2 * π)) = g s₀ + k * (2 * π) := fw_angle_add_int (G 0) c₀ s₀ k
    rw [this]
    linarith
  have hb := hgm.lt_iff_lt.1 hg1
  rw [lt_div_iff₀ (by positivity)]
  have h00 : β 0 = s₀ := hβ.2.1
  linarith

end

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution (φ G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ContinuousOn G (Set.Icc 0 1)) (hGd : ∀ t ∈ Set.Icc (0 : ℝ) 1, (G t).det = 1)
    (hG1 : G 1 = G 0) (θ : ℝ → ℝ) (hθc : ContinuousOn θ (Set.Icc 0 1)) (hθ1 : θ 1 = θ 0)
    (hθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧
      (G t * (G 0)⁻¹).mulVec (rotationVector 0) = r • rotationVector (θ t)) (k : ℤ)
    (h : ∀ d ∈ windingInterval (fun t => G t * φ t * (G 0)⁻¹), (k : ℝ) < d) :
    ∀ d ∈ windingInterval φ, (k : ℝ) < d :=
  lt_of_mem_windingInterval_of_conj_of_loop_aux φ G hGc hGd hG1 θ hθc hθ1 hθ k h
