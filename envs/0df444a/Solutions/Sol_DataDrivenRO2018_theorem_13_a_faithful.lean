-- Prove2me | solution 1 for DataDrivenRO2018.theorem_13_a_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:50:47.179828+00:00
-- url     : https://prove2.me/submissions/b76637e5-5cac-436d-a66f-df38e9735333

import Mathlib
import Definitions.Def_DataDrivenRO_Moment_Setting
import Definitions.Def_RobustMDP_Shared_supportFunction

open Matrix

namespace DD86

/-- The Euclidean norm `enorm` as the norm of `EuclideanSpace`. -/
lemma enorm_eq {d : ℕ} (v : Fin d → ℝ) :
    DataDrivenRO.Moment.enorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq, DataDrivenRO.Moment.enorm]; simp [dotProduct, sq]

lemma dot_eq {d : ℕ} (a b : Fin d → ℝ) :
    a ⬝ᵥ b = inner ℝ (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 b) := by
  simp [dotProduct, PiLp.inner_apply, mul_comm]

lemma enorm_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ DataDrivenRO.Moment.enorm v := by
  rw [enorm_eq]; exact norm_nonneg _

/-- Cauchy–Schwarz on a ball. -/
lemma ball_le {d : ℕ} {r : ℝ} {y : Fin d → ℝ} (hy : DataDrivenRO.Moment.enorm y ≤ r)
    (v : Fin d → ℝ) : y ⬝ᵥ v ≤ r * DataDrivenRO.Moment.enorm v := by
  rw [dot_eq]
  refine (real_inner_le_norm _ _).trans ?_
  rw [← enorm_eq, ← enorm_eq]
  exact mul_le_mul_of_nonneg_right hy (enorm_nonneg v)

/-- The maximum over a ball is attained. -/
lemma ball_max {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (v : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, DataDrivenRO.Moment.enorm y ≤ r ∧
      y ⬝ᵥ v = r * DataDrivenRO.Moment.enorm v := by
  by_cases hv : DataDrivenRO.Moment.enorm v = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [enorm_eq]; simpa using hr
    · simp [hv]
  · refine ⟨(r / DataDrivenRO.Moment.enorm v) • v, ?_, ?_⟩
    · rw [enorm_eq, WithLp.toLp_smul, norm_smul, ← enorm_eq, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hr (enorm_nonneg v)), div_mul_cancel₀ _ hv]
    · rw [smul_dotProduct, smul_eq_mul]
      have : v ⬝ᵥ v = DataDrivenRO.Moment.enorm v ^ 2 := by
        rw [DataDrivenRO.Moment.enorm, Real.sq_sqrt]
        exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
      rw [this]; field_simp

lemma transpose_dot {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (w v : Fin d → ℝ) :
    (C.transpose *ᵥ w) ⬝ᵥ v = w ⬝ᵥ (C *ᵥ v) := by
  rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose, Matrix.dotProduct_mulVec]

/-- Closed form of the support function of the uncertainty set (35). -/
lemma support_eq {d : ℕ} (μhat : Fin d → ℝ) (C : Matrix (Fin d) (Fin d) ℝ) {Γ₁ : ℝ}
    (hΓ₁ : 0 ≤ Γ₁) (ε : ℝ) (v : Fin d → ℝ) :
    RobustMDP.Shared.supportFunction (DataDrivenRO.Moment.UCS μhat C Γ₁ ε) v =
      μhat ⬝ᵥ v + Γ₁ * DataDrivenRO.Moment.enorm v +
        Real.sqrt (1 / ε - 1) * DataDrivenRO.Moment.enorm (C *ᵥ v) := by
  unfold RobustMDP.Shared.supportFunction
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨y, hy, hyv⟩ := ball_max hΓ₁ v
    obtain ⟨w, hw, hwv⟩ := ball_max (Real.sqrt_nonneg (1 / ε - 1)) (C *ᵥ v)
    refine ⟨μhat + y + C.transpose *ᵥ w, ⟨y, w, hy, hw, rfl⟩, ?_⟩
    change (μhat + y + C.transpose *ᵥ w) ⬝ᵥ v = _
    rw [add_dotProduct, add_dotProduct, transpose_dot, hyv, hwv]
  · rintro _ ⟨u, ⟨y, w, hy, hw, rfl⟩, rfl⟩
    change (μhat + y + C.transpose *ᵥ w) ⬝ᵥ v ≤ _
    rw [add_dotProduct, add_dotProduct, transpose_dot]
    have h1 := ball_le hy v
    have h2 := ball_le hw (C *ᵥ v)
    linarith

/-- `enorm ∘ A` is convex for a linear map `A`. -/
lemma convex_enorm_comp {E : Type*} [AddCommGroup E] [Module ℝ E] {d : ℕ}
    (A : E →ₗ[ℝ] (Fin d → ℝ)) :
    ConvexOn ℝ Set.univ (fun p => DataDrivenRO.Moment.enorm (A p)) := by
  have h := (convexOn_norm (E := EuclideanSpace ℝ (Fin d)) convex_univ).comp_linearMap
    ((WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toLinearMap ∘ₗ A)
  simp only [Set.preimage_univ] at h
  convert h using 2 with p
  rw [enorm_eq]; rfl

/-- `ε ↦ √(1/ε - 1)` is convex on `(0, 3/4)`. -/
lemma convex_sqrt : ConvexOn ℝ (Set.Ioo (0 : ℝ) (3 / 4)) (fun ε => Real.sqrt (1 / ε - 1)) := by
  have hD : ∀ x ∈ Set.Ioo (0 : ℝ) (3 / 4),
      HasDerivAt (fun ε => Real.sqrt (1 / ε - 1)) (-1 / (2 * Real.sqrt (x ^ 3 * (1 - x)))) x := by
    rintro x ⟨h0, h1⟩
    have hpos : 0 < 1 / x - 1 := by
      rw [sub_pos, lt_div_iff₀ h0]; linarith
    have hd2 : HasDerivAt (fun ε => 1 / ε - 1) (-(x ^ 2)⁻¹) x := by
      simpa only [one_div] using (hasDerivAt_inv h0.ne').sub_const 1
    have := hd2.sqrt hpos.ne'
    convert this using 1
    have hs : Real.sqrt (x ^ 3 * (1 - x)) = x ^ 2 * Real.sqrt (1 / x - 1) := by
      rw [show x ^ 3 * (1 - x) = (x ^ 2) ^ 2 * (1 / x - 1) by field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [hs]
    have : 0 < Real.sqrt (1 / x - 1) := Real.sqrt_pos.mpr hpos
    field_simp
  apply MonotoneOn.convexOn_of_deriv (convex_Ioo _ _)
  · intro x hx
    exact (hD x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioo]; intro x hx; exact (hD x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro x hx y hy hxy
    rw [(hD x hx).deriv, (hD y hy).deriv]
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    have ha : 0 < x ^ 3 * (1 - x) := by apply mul_pos; positivity; linarith
    have hbr : 0 ≤ x ^ 2 + x * y + y ^ 2 - (x + y) * (x ^ 2 + y ^ 2) := by
      nlinarith [mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1), mul_pos hx0 hy0, mul_pos hx0 hx0,
        mul_pos hy0 hy0, mul_pos (mul_pos hx0 hy0) (sub_pos.mpr hx1), mul_pos (mul_pos hx0 hy0) (sub_pos.mpr hy1),
        mul_pos (mul_pos hx0 hx0) (sub_pos.mpr hy1), mul_pos (mul_pos hy0 hy0) (sub_pos.mpr hx1),
        mul_pos (mul_pos hx0 hx0) (sub_pos.mpr hx1), mul_pos (mul_pos hy0 hy0) (sub_pos.mpr hy1)]
    have hab : x ^ 3 * (1 - x) ≤ y ^ 3 * (1 - y) := by
      have : y ^ 3 * (1 - y) - x ^ 3 * (1 - x) =
        (y - x) * (x ^ 2 + x * y + y ^ 2 - (x + y) * (x ^ 2 + y ^ 2)) := by ring
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hbr]
    have hsa : 0 < Real.sqrt (x ^ 3 * (1 - x)) := Real.sqrt_pos.mpr ha
    have hsb : Real.sqrt (x ^ 3 * (1 - x)) ≤ Real.sqrt (y ^ 3 * (1 - y)) := Real.sqrt_le_sqrt hab
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith

end DD86

open DD86 in
theorem solution {d : ℕ} (Γ₁ Γ₂ : ℝ)
    (μhat : Fin d → ℝ) (Shat C : Matrix (Fin d) (Fin d) ℝ)
    (hΓ₁ : 0 ≤ Γ₁) (hΓ₂ : 0 ≤ Γ₂)
    (hC : C.transpose * C = Shat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    (∀ ε : ℝ, 0 < ε → ε < 3 / 4 →
      ConvexOn ℝ Set.univ (fun p : (Fin d → ℝ) × ℝ =>
        RobustMDP.Shared.supportFunction (DataDrivenRO.Moment.UCS μhat C Γ₁ ε) p.1 - p.2)) ∧
    (∀ (v : Fin d → ℝ) (t : ℝ),
      ConvexOn ℝ (Set.Ioo (0 : ℝ) (3 / 4)) (fun ε : ℝ =>
        RobustMDP.Shared.supportFunction (DataDrivenRO.Moment.UCS μhat C Γ₁ ε) v - t)) := by
  constructor
  · intro ε _ _
    simp only [support_eq μhat C hΓ₁]
    let L1 : (Fin d → ℝ) × ℝ →ₗ[ℝ] ℝ :=
      { toFun := fun p => μhat ⬝ᵥ p.1 - p.2
        map_add' := fun p q => by simp [dotProduct_add]; ring
        map_smul' := fun c p => by simp [dotProduct_smul]; ring }
    have hlin : ConvexOn ℝ Set.univ (fun p : (Fin d → ℝ) × ℝ => μhat ⬝ᵥ p.1 - p.2) := by
      have := L1.convexOn convex_univ
      exact this
    have h1 := convex_enorm_comp (LinearMap.fst ℝ (Fin d → ℝ) ℝ)
    have h2 := convex_enorm_comp ((Matrix.mulVecLin C).comp (LinearMap.fst ℝ (Fin d → ℝ) ℝ))
    have := (hlin.add (h1.smul hΓ₁)).add (h2.smul (Real.sqrt_nonneg (1 / ε - 1)))
    refine this.congr (fun p _ => ?_)
    simp only [Pi.add_apply, smul_eq_mul, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_fst, Matrix.mulVecLin_apply]
    ring
  · intro v t
    simp only [support_eq μhat C hΓ₁]
    have := (convex_sqrt.smul (enorm_nonneg (C *ᵥ v))).add_const
      (μhat ⬝ᵥ v + Γ₁ * DataDrivenRO.Moment.enorm v - t)
    refine this.congr (fun ε _ => ?_)
    simp only [Pi.add_apply, smul_eq_mul]
    ring
