-- Prove2me | solution 1 for DataDrivenRO.Moment.cauchy_schwarz_steps
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:19:53.111463+00:00
-- url     : https://prove2.me/submissions/4d2884b6-aa5c-4f39-a365-a1aae895ad9e

import Mathlib
import Definitions.Def_DataDrivenRO_Moment_Setting

theorem p1feb_cs {d : ℕ} (u y : Fin d → ℝ) :
    u ⬝ᵥ y ≤ DataDrivenRO.Moment.enorm u * DataDrivenRO.Moment.enorm y := by
  unfold DataDrivenRO.Moment.enorm
  have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u y
  simpa [dotProduct, sq] using this

theorem p1feb_key {d : ℕ} (u : Fin d → ℝ) (R : ℝ) (hR : 0 ≤ R) :
    IsGreatest ((fun y : Fin d → ℝ => u ⬝ᵥ y) '' {y | DataDrivenRO.Moment.enorm y ≤ R})
      (R * DataDrivenRO.Moment.enorm u) := by
  have hn : 0 ≤ u ⬝ᵥ u := by
    simpa [dotProduct] using Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (u i))
  have hsq : DataDrivenRO.Moment.enorm u ^ 2 = u ⬝ᵥ u := Real.sq_sqrt hn
  have he : 0 ≤ DataDrivenRO.Moment.enorm u := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · rcases he.eq_or_lt with h | h
    · refine ⟨0, ?_, ?_⟩
      · show DataDrivenRO.Moment.enorm (0 : Fin d → ℝ) ≤ R
        simp [DataDrivenRO.Moment.enorm, hR]
      · simp [← h]
    · have he0 : DataDrivenRO.Moment.enorm u ≠ 0 := h.ne'
      refine ⟨(R / DataDrivenRO.Moment.enorm u) • u, ?_, ?_⟩
      · show DataDrivenRO.Moment.enorm _ ≤ R
        have hh : ((R / DataDrivenRO.Moment.enorm u) • u) ⬝ᵥ
            ((R / DataDrivenRO.Moment.enorm u) • u) = R ^ 2 := by
          rw [smul_dotProduct, dotProduct_smul, ← hsq, smul_eq_mul, smul_eq_mul]
          field_simp
        have hdef : DataDrivenRO.Moment.enorm ((R / DataDrivenRO.Moment.enorm u) • u) =
            Real.sqrt (((R / DataDrivenRO.Moment.enorm u) • u) ⬝ᵥ
              ((R / DataDrivenRO.Moment.enorm u) • u)) := rfl
        simp only [hdef, hh, Real.sqrt_sq hR, le_refl]
      · show u ⬝ᵥ ((R / DataDrivenRO.Moment.enorm u) • u) = R * DataDrivenRO.Moment.enorm u
        rw [dotProduct_smul, ← hsq, smul_eq_mul]
        field_simp
  · rintro _ ⟨y, hy, rfl⟩
    calc u ⬝ᵥ y ≤ DataDrivenRO.Moment.enorm u * DataDrivenRO.Moment.enorm y := p1feb_cs u y
      _ ≤ DataDrivenRO.Moment.enorm u * R := mul_le_mul_of_nonneg_left hy he
      _ = R * DataDrivenRO.Moment.enorm u := mul_comm _ _

/-- The two Cauchy–Schwarz maximizations cited in EC.1.7, p. ec8. -/
theorem solution {d : ℕ} (Γ₁ Γ₂ r : ℝ)
    (Shat C : Matrix (Fin d) (Fin d) ℝ)
    (hΓ₁ : 0 ≤ Γ₁) (hΓ₂ : 0 ≤ Γ₂) (hr : 0 ≤ r)
    (hC : C.transpose * C = Shat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ))
    (v : Fin d → ℝ) :
    IsGreatest ((fun y : Fin d → ℝ => v ⬝ᵥ y) '' {y | DataDrivenRO.Moment.enorm y ≤ Γ₁})
        (Γ₁ * DataDrivenRO.Moment.enorm v) ∧
    IsGreatest ((fun w : Fin d → ℝ => v ⬝ᵥ Matrix.mulVec C.transpose w) ''
        {w | DataDrivenRO.Moment.enorm w ≤ r}) (r * DataDrivenRO.Moment.enorm (Matrix.mulVec C v)) ∧
    DataDrivenRO.Moment.enorm (Matrix.mulVec C v) =
      Real.sqrt (v ⬝ᵥ Matrix.mulVec (Shat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ)) v) := by
  refine ⟨p1feb_key v Γ₁ hΓ₁, ?_, ?_⟩
  · have hf : (fun w : Fin d → ℝ => v ⬝ᵥ Matrix.mulVec C.transpose w) =
        fun w => (Matrix.mulVec C v) ⬝ᵥ w := by
      funext w
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [hf]
    exact p1feb_key _ r hr
  · unfold DataDrivenRO.Moment.enorm
    congr 1
    rw [← hC, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose]
