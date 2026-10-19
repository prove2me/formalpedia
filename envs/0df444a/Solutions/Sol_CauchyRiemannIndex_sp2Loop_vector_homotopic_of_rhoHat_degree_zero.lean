-- Prove2me | solution 1 for CauchyRiemannIndex.sp2Loop_vector_homotopic_of_rhoHat_degree_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T17:26:01.109567+00:00
-- url     : https://prove2.me/submissions/be34f475-b764-40e9-b995-97ea3c9be939

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_complexLoop_homotopic_const_of_argLift

open Matrix

namespace CRLK6

open CauchyRiemannIndex

/-- The vector `(x.re, x.im)` of `ℝ² = Fin 1 ⊕ Fin 1 → ℝ`. -/
def toVec (x : ℂ) : Fin 1 ⊕ Fin 1 → ℝ := Sum.elim (fun _ => x.re) (fun _ => x.im)

lemma continuous_toVec : Continuous toVec := by
  refine continuous_pi fun i => ?_
  rcases i with i | i <;> simp only [toVec, Sum.elim_inl, Sum.elim_inr] <;> fun_prop

lemma toVec_ne_zero {x : ℂ} (hx : x ≠ 0) : toVec x ≠ 0 := by
  intro h
  apply hx
  have h1 := congrFun h (Sum.inl 0)
  have h2 := congrFun h (Sum.inr 0)
  simp only [toVec, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply] at h1 h2
  exact Complex.ext h1 h2

lemma toVec_one : toVec 1 = Pi.single (Sum.inl 0) 1 := by
  funext i
  rcases i with i | i
  · rw [Subsingleton.elim i 0]; simp [toVec]
  · simp [toVec]

/-- The complex number `a + i c` of the first column `(a, c)` of `A`. -/
def col (A : Mat 1) : ℂ := ⟨A (Sum.inl 0) (Sum.inl 0), A (Sum.inr 0) (Sum.inl 0)⟩

lemma toVec_col (A : Mat 1) : toVec (col A) = A *ᵥ Pi.single (Sum.inl 0) 1 := by
  funext i
  rcases i with i | i <;> rw [Subsingleton.elim i 0] <;>
    simp [toVec, col, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma complexLinearDet_eq (A : Mat 1) : complexLinearDet A =
    ⟨(A (Sum.inl 0) (Sum.inl 0) + A (Sum.inr 0) (Sum.inr 0)) / 2,
      (A (Sum.inr 0) (Sum.inl 0) - A (Sum.inl 0) (Sum.inr 0)) / 2⟩ := by
  unfold complexLinearDet complexLinearPart
  rw [Matrix.det_unique]
  apply Complex.ext <;>
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks] <;> ring

lemma det_eq_one {A : Mat 1} (hA : IsSymplectic A) :
    A (Sum.inl 0) (Sum.inl 0) * A (Sum.inr 0) (Sum.inr 0) -
      A (Sum.inl 0) (Sum.inr 0) * A (Sum.inr 0) (Sum.inl 0) = 1 := by
  have h := congrFun (congrFun ((SymplecticGroup.mem_iff).1 hA) (Sum.inl 0)) (Sum.inr 0)
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks] at h
  linarith

lemma re_det_mul_conj_col {A : Mat 1} (hA : IsSymplectic A) :
    (complexLinearDet A * (starRingEnd ℂ) (col A)).re =
      (A (Sum.inl 0) (Sum.inl 0) ^ 2 + A (Sum.inr 0) (Sum.inl 0) ^ 2 + 1) / 2 := by
  have h := det_eq_one hA
  rw [complexLinearDet_eq]
  simp only [col, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  linear_combination h / 2

lemma col_ne_zero {A : Mat 1} (hA : IsSymplectic A) : col A ≠ 0 := by
  intro h
  have := re_det_mul_conj_col hA
  rw [h, map_zero, mul_zero, Complex.zero_re] at this
  nlinarith [sq_nonneg (A (Sum.inl 0) (Sum.inl 0)), sq_nonneg (A (Sum.inr 0) (Sum.inl 0))]

lemma det_ne_zero {A : Mat 1} (hA : IsSymplectic A) : complexLinearDet A ≠ 0 := by
  intro h
  have := re_det_mul_conj_col hA
  rw [h, zero_mul, Complex.zero_re] at this
  nlinarith [sq_nonneg (A (Sum.inl 0) (Sum.inl 0)), sq_nonneg (A (Sum.inr 0) (Sum.inl 0))]

/-- The unit vector `z / |z|`. -/
noncomputable def unit (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

lemma norm_unit {z : ℂ} (hz : z ≠ 0) : ‖unit z‖ = 1 := by
  unfold unit
  rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hz)]

lemma re_unit_mul_conj_pos {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) (h : 0 < (w * (starRingEnd ℂ) z).re) :
    0 < (unit z * (starRingEnd ℂ) (unit w)).re := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have e : unit z * (starRingEnd ℂ) (unit w) =
      (((‖z‖ * ‖w‖)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) (w * (starRingEnd ℂ) z) := by
    unfold unit
    rw [map_div₀, Complex.conj_ofReal, map_mul, Complex.conj_conj]
    push_cast
    field_simp
  rw [e, Complex.re_ofReal_mul, Complex.conj_re]
  positivity

lemma col_one : col (1 : Mat 1) = 1 := by
  apply Complex.ext <;> simp [col]

lemma complexLinearDet_one : complexLinearDet (1 : Mat 1) = 1 := by
  rw [complexLinearDet_eq]; apply Complex.ext <;> simp

lemma unit_one : unit 1 = 1 := by simp [unit]

theorem main
    (φ : C(unitInterval, Mat 1)) (hs : ∀ t, IsSymplectic (φ t)) (h0 : φ 0 = 1)
    (h1 : φ 1 = 1) (θ : unitInterval → ℝ) (hθ : IsArgLift (fun t => rhoHat (φ t)) θ)
    (hθ1 : θ 1 = θ 0) :
    ∃ H : C(unitInterval × unitInterval, Fin 1 ⊕ Fin 1 → ℝ),
      (∀ t, H (0, t) = φ t *ᵥ Pi.single (Sum.inl 0) 1) ∧
      (∀ t, H (1, t) = Pi.single (Sum.inl 0) 1) ∧ (∀ p, H p ≠ 0) ∧
      (∀ s, H (s, 0) = Pi.single (Sum.inl 0) 1) ∧ ∀ s, H (s, 1) = Pi.single (Sum.inl 0) 1 := by
  have hcoef : ∀ i j, Continuous fun t => φ t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp φ.continuous)
  have hzc : Continuous fun t => col (φ t) := by
    have e : (fun t => col (φ t)) = fun t => ((φ t (Sum.inl 0) (Sum.inl 0) : ℝ) : ℂ) +
        ((φ t (Sum.inr 0) (Sum.inl 0) : ℝ) : ℂ) * Complex.I := by
      funext t; exact Complex.mk_eq_add_mul_I _ _
    rw [e]
    have := hcoef (Sum.inl 0) (Sum.inl 0)
    have := hcoef (Sum.inr 0) (Sum.inl 0)
    fun_prop
  have hwc : Continuous fun t => complexLinearDet (φ t) := by
    have e : (fun t => complexLinearDet (φ t)) = fun t =>
        (((φ t (Sum.inl 0) (Sum.inl 0) + φ t (Sum.inr 0) (Sum.inr 0)) / 2 : ℝ) : ℂ) +
        (((φ t (Sum.inr 0) (Sum.inl 0) - φ t (Sum.inl 0) (Sum.inr 0)) / 2 : ℝ) : ℂ) * Complex.I := by
      funext t; rw [complexLinearDet_eq]; exact Complex.mk_eq_add_mul_I _ _
    rw [e]
    have := hcoef (Sum.inl 0) (Sum.inl 0)
    have := hcoef (Sum.inr 0) (Sum.inl 0)
    have := hcoef (Sum.inl 0) (Sum.inr 0)
    have := hcoef (Sum.inr 0) (Sum.inr 0)
    fun_prop
  have hunitc : ∀ f : unitInterval → ℂ, Continuous f → (∀ t, f t ≠ 0) →
      Continuous fun t => unit (f t) := fun f hf hf0 =>
    hf.div (Complex.continuous_ofReal.comp (continuous_norm.comp hf))
      (fun t => by exact_mod_cast norm_ne_zero_iff.2 (hf0 t))
  have hzu := hunitc _ hzc (fun t => col_ne_zero (hs t))
  have hwu := hunitc _ hwc (fun t => det_ne_zero (hs t))
  set q : unitInterval → ℂ := fun t => unit (col (φ t)) * (starRingEnd ℂ) (unit (complexLinearDet (φ t)))
    with hqdef
  have hqc : Continuous q := hzu.mul (Complex.continuous_conj.comp hwu)
  have hq : ∀ t, 0 < (q t).re := fun t =>
    re_unit_mul_conj_pos (col_ne_zero (hs t)) (det_ne_zero (hs t))
      (by rw [re_det_mul_conj_col (hs t)]; positivity)
  have hqn : ∀ t, ‖q t‖ = 1 := fun t => by
    simp only [hqdef, norm_mul, Complex.norm_conj, norm_unit (col_ne_zero (hs t)),
      norm_unit (det_ne_zero (hs t)), mul_one]
  have hrho : ∀ t, rhoHat (φ t) = unit (complexLinearDet (φ t)) := fun t => rfl
  set θ' : unitInterval → ℝ := fun t => θ t + Complex.arg (q t) with hθ'def
  have hθ'c : Continuous θ' := hθ.1.add (continuous_iff_continuousAt.2 fun t =>
    (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.2 (Or.inl (hq t)))).comp hqc.continuousAt)
  have hlift : IsArgLift (fun t => col (φ t) / (‖col (φ t)‖ : ℂ)) θ' := by
    refine ⟨hθ'c, fun t => ?_⟩
    have ha := Complex.norm_mul_exp_arg_mul_I (q t)
    rw [hqn t, Complex.ofReal_one, one_mul] at ha
    simp only [hθ'def]
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, ← hθ.2 t, ha]
    show unit (col (φ t)) = rhoHat (φ t) * (unit (col (φ t)) *
      (starRingEnd ℂ) (unit (complexLinearDet (φ t))))
    rw [hrho, mul_left_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_unit (det_ne_zero (hs t))]
    simp
  have hq0 : ∀ t, φ t = 1 → q t = 1 := fun t ht => by
    simp only [hqdef, ht, col_one, complexLinearDet_one, unit_one, map_one, mul_one]
  have hθ'1 : θ' 1 = θ' 0 := by
    simp only [hθ'def, hq0 1 h1, hq0 0 h0, Complex.arg_one, hθ1]
  obtain ⟨H, hH0, hH1, hHne, hHs0, hHs1⟩ :=
    complexLoop_homotopic_const_of_argLift ⟨fun t => col (φ t), hzc⟩ (fun t => col_ne_zero (hs t))
      (by show col (φ 1) = col (φ 0); rw [h0, h1]) θ' hlift hθ'1
  have hv0 : (⟨fun t => col (φ t), hzc⟩ : C(unitInterval, ℂ)) 0 = 1 := by
    show col (φ 0) = 1; rw [h0, col_one]
  rw [hv0] at hH1 hHs0 hHs1
  refine ⟨⟨fun p => toVec (H p), continuous_toVec.comp H.continuous⟩, fun t => ?_, fun t => ?_,
    fun p => toVec_ne_zero (hHne p), fun s => ?_, fun s => ?_⟩
  · show toVec (H (0, t)) = _; rw [hH0]; exact toVec_col _
  · show toVec (H (1, t)) = _; rw [hH1]; exact toVec_one
  · show toVec (H (s, 0)) = _; rw [hHs0]; exact toVec_one
  · show toVec (H (s, 1)) = _; rw [hHs1]; exact toVec_one

end CRLK6

open CauchyRiemannIndex

open Matrix

theorem solution
    (φ : C(unitInterval, Mat 1)) (hs : ∀ t, IsSymplectic (φ t)) (h0 : φ 0 = 1)
    (h1 : φ 1 = 1) (θ : unitInterval → ℝ) (hθ : IsArgLift (fun t => rhoHat (φ t)) θ)
    (hθ1 : θ 1 = θ 0) :
    ∃ H : C(unitInterval × unitInterval, Fin 1 ⊕ Fin 1 → ℝ),
      (∀ t, H (0, t) = φ t *ᵥ Pi.single (Sum.inl 0) 1) ∧
      (∀ t, H (1, t) = Pi.single (Sum.inl 0) 1) ∧ (∀ p, H p ≠ 0) ∧
      (∀ s, H (s, 0) = Pi.single (Sum.inl 0) 1) ∧ ∀ s, H (s, 1) = Pi.single (Sum.inl 0) 1 :=
  CRLK6.main φ hs h0 h1 θ hθ hθ1
