-- Prove2me | solution 1 for FeaturePricing.Ellipsoid.closed_form_bounds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:39:41.839931+00:00
-- url     : https://prove2.me/submissions/c4af248e-80cf-41b8-bc4f-2eea5478d7e6

import Mathlib
import Definitions.Def_FeaturePricing_Ellipsoid_EllipsoidPricing

set_option autoImplicit false
open Matrix LinearOptimization FeaturePricing.Ellipsoid

/-- Cauchy–Schwarz for a positive semidefinite form. -/
theorem FPE_cs {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef)
    (v w : Fin d → ℝ) :
    (v ⬝ᵥ B *ᵥ w) ^ 2 ≤ (v ⬝ᵥ B *ᵥ v) * (w ⬝ᵥ B *ᵥ w) := by
  have hsymm : ∀ u u' : Fin d → ℝ, u ⬝ᵥ B *ᵥ u' = u' ⬝ᵥ B *ᵥ u := by
    intro u u'
    have h := hB.isHermitian
    have h' : Bᵀ = B := by
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using h.eq
    have e : u ᵥ* B = B *ᵥ u := by
      have := Matrix.vecMul_transpose B u
      rwa [h'] at this
    rw [Matrix.dotProduct_mulVec, e, dotProduct_comm]
  have key : ∀ t : ℝ, 0 ≤ (w ⬝ᵥ B *ᵥ w) * (t * t) + (2 * (v ⬝ᵥ B *ᵥ w)) * t + (v ⬝ᵥ B *ᵥ v) := by
    intro t
    have h0 := hB.dotProduct_mulVec_nonneg (v + t • w)
    have : (v + t • w) ⬝ᵥ B *ᵥ (v + t • w) =
        (w ⬝ᵥ B *ᵥ w) * (t * t) + (2 * (v ⬝ᵥ B *ᵥ w)) * t + (v ⬝ᵥ B *ᵥ v) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [hsymm w v]
      ring
    simpa [this] using h0
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem FPE_psd_nonneg {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (x : Fin d → ℝ) :
    0 ≤ x ⬝ᵥ A *ᵥ x := hA.posSemidef.dotProduct_mulVec_nonneg x

theorem FPE_inv_mulVec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (x : Fin d → ℝ) :
    A⁻¹ *ᵥ (A *ᵥ x) = x := by
  have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]

/-- Every point of the ellipsoid has `|x'(θ - a)| ≤ √(x'Ax)`. -/
theorem FPE_ellipsoid_bound {d : ℕ} (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (x θ : Fin d → ℝ) (hθ : θ ∈ ellipsoid a A) :
    (x ⬝ᵥ θ - x ⬝ᵥ a) ^ 2 ≤ x ⬝ᵥ A *ᵥ x := by
  have h := FPE_cs A⁻¹ hA.inv.posSemidef (θ - a) (A *ᵥ x)
  rw [FPE_inv_mulVec A hA x] at h
  have e1 : (θ - a) ⬝ᵥ x = x ⬝ᵥ θ - x ⬝ᵥ a := by
    rw [dotProduct_comm, dotProduct_sub]
  have e2 : (A *ᵥ x) ⬝ᵥ x = x ⬝ᵥ A *ᵥ x := dotProduct_comm _ _
  rw [e1, e2] at h
  have hθ' : (θ - a) ⬝ᵥ A⁻¹ *ᵥ (θ - a) ≤ 1 := hθ
  have hq := FPE_psd_nonneg A hA x
  calc (x ⬝ᵥ θ - x ⬝ᵥ a) ^ 2 ≤ _ := h
    _ ≤ 1 * (x ⬝ᵥ A *ᵥ x) := mul_le_mul_of_nonneg_right hθ' hq
    _ = _ := one_mul _

theorem solution {d : ℕ} (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (x : Fin d → ℝ) :
    IsLeast ((fun θ => x ⬝ᵥ θ) '' ellipsoid a A) (x ⬝ᵥ a - Real.sqrt (x ⬝ᵥ A *ᵥ x)) ∧
    IsGreatest ((fun θ => x ⬝ᵥ θ) '' ellipsoid a A) (x ⬝ᵥ a + Real.sqrt (x ⬝ᵥ A *ᵥ x)) := by
  have hq := FPE_psd_nonneg A hA x
  have hbd : ∀ θ ∈ ellipsoid a A, |x ⬝ᵥ θ - x ⬝ᵥ a| ≤ Real.sqrt (x ⬝ᵥ A *ᵥ x) := fun θ hθ =>
    Real.abs_le_sqrt (FPE_ellipsoid_bound a A hA x θ hθ)
  have hmem : ∀ θ : Fin d → ℝ, ∀ c : ℝ, Real.sqrt (x ⬝ᵥ A *ᵥ x) ≠ 0 →
      θ = a + c • (A *ᵥ x) → c ^ 2 * (x ⬝ᵥ A *ᵥ x) ≤ 1 → θ ∈ ellipsoid a A := by
    intro θ c _ hθ hc
    have : (θ - a) ⬝ᵥ A⁻¹ *ᵥ (θ - a) = c ^ 2 * (x ⬝ᵥ A *ᵥ x) := by
      have : θ - a = c • (A *ᵥ x) := by rw [hθ]; abel
      rw [this, Matrix.mulVec_smul, FPE_inv_mulVec A hA x]
      simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [dotProduct_comm (A *ᵥ x) x]
      ring
    show (θ - a) ⬝ᵥ A⁻¹ *ᵥ (θ - a) ≤ 1
    rw [this]; exact hc
  by_cases h0 : Real.sqrt (x ⬝ᵥ A *ᵥ x) = 0
  · have hq0 : x ⬝ᵥ A *ᵥ x = 0 := by
      rcases (Real.sqrt_eq_zero hq).1 h0 with h; exact h
    have hx : x = 0 := by
      by_contra hne
      have := hA.dotProduct_mulVec_pos hne
      simp only [star_trivial] at this
      linarith
    subst hx
    have ha : a ∈ ellipsoid a A := by
      show (a - a) ⬝ᵥ A⁻¹ *ᵥ (a - a) ≤ 1
      simp
    rw [h0]
    refine ⟨⟨⟨a, ha, by simp⟩, ?_⟩, ⟨⟨a, ha, by simp⟩, ?_⟩⟩ <;>
    · rintro _ ⟨θ, _, rfl⟩; simp
  · have hpos : 0 < Real.sqrt (x ⬝ᵥ A *ᵥ x) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
    set s := Real.sqrt (x ⬝ᵥ A *ᵥ x) with hs
    have hs2 : s ^ 2 = x ⬝ᵥ A *ᵥ x := Real.sq_sqrt hq
    have hval : ∀ c : ℝ, x ⬝ᵥ (a + c • (A *ᵥ x)) = x ⬝ᵥ a + c * (x ⬝ᵥ A *ᵥ x) := by
      intro c
      simp [dotProduct_add, dotProduct_smul]
    have hc : (1 / s) ^ 2 * (x ⬝ᵥ A *ᵥ x) ≤ 1 := by
      rw [← hs2]; field_simp; exact le_refl _
    have hc' : (-(1 / s)) ^ 2 * (x ⬝ᵥ A *ᵥ x) ≤ 1 := by
      rw [neg_sq]; exact hc
    refine ⟨⟨⟨a + (-(1 / s)) • (A *ᵥ x), hmem _ _ h0 rfl hc', ?_⟩, ?_⟩,
      ⟨⟨a + (1 / s) • (A *ᵥ x), hmem _ _ h0 rfl hc, ?_⟩, ?_⟩⟩
    · show x ⬝ᵥ (a + (-(1 / s)) • (A *ᵥ x)) = x ⬝ᵥ a - s
      rw [hval, ← hs2]; field_simp; ring
    · rintro _ ⟨θ, hθ, rfl⟩
      have := (abs_le.1 (hbd θ hθ)).1
      show x ⬝ᵥ a - s ≤ x ⬝ᵥ θ
      linarith
    · show x ⬝ᵥ (a + (1 / s) • (A *ᵥ x)) = x ⬝ᵥ a + s
      rw [hval, ← hs2]; field_simp
    · rintro _ ⟨θ, hθ, rfl⟩
      have := (abs_le.1 (hbd θ hθ)).2
      show x ⬝ᵥ θ ≤ x ⬝ᵥ a + s
      linarith
