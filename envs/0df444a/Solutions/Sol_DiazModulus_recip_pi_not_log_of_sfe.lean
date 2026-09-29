-- Prove2me | solution 1 for DiazModulus.recip_pi_not_log_of_sfe
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T19:08:45.401986+00:00
-- url     : https://prove2.me/submissions/350525c2-5b54-4fca-94bb-08c32c6c6488

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

namespace DiazModulus

/-- Algebraic numbers: closure helpers (same `Qbar`-subfield pattern as
`DZ_SPLITS_core` / `XX_RP_gamma_shape`). -/
theorem XX1_alg_mul {z w : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w) :
    IsAlgebraic ℚ (z * w) := by
  rw [← mem_Qbar_iff] at *
  exact Subfield.mul_mem _ hz hw

theorem XX1_alg_neg {z : ℂ} (hz : IsAlgebraic ℚ z) : IsAlgebraic ℚ (-z) := by
  rw [← mem_Qbar_iff] at *
  exact Subfield.neg_mem _ hz

theorem XX1_alg_div {z w : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w) :
    IsAlgebraic ℚ (z / w) := by
  rw [← mem_Qbar_iff] at *
  exact Subfield.div_mem _ hz hw

/-- `iπ` is transcendental from Hermite–Lindemann alone. -/
theorem XX1_ipi_transcendental_of_hl (hHL : HermiteLindemann) :
    Transcendental ℚ (((Real.pi : ℝ) : ℂ) * Complex.I) := by
  intro halg
  have h0 : ((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero _ Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hT := hHL _ h0 halg
  rw [Complex.exp_pi_mul_I] at hT
  exact hT (XX1_alg_neg isAlgebraic_one)

/-- `λ = γ/(iπ)` is transcendental from Hermite–Lindemann alone: otherwise
`iπ = γ/λ` would be algebraic. -/
theorem XX1_lambda_transcendental_of_hl (hHL : HermiteLindemann)
    {γ : ℂ} (hγ : IsAlgebraic ℚ γ) (hγ0 : γ ≠ 0) :
    Transcendental ℚ (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) := by
  intro halg
  have hpiI0 : ((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero _ Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hlam0 : γ / (((Real.pi : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    div_ne_zero hγ0 hpiI0
  have hpiI : ((Real.pi : ℝ) : ℂ) * Complex.I =
      γ / (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) := by
    have hcancel : γ / (((Real.pi : ℝ) : ℂ) * Complex.I) *
        (((Real.pi : ℝ) : ℂ) * Complex.I) = γ := div_mul_cancel₀ _ hpiI0
    rw [eq_div_iff hlam0]
    linear_combination hcancel
  exact (XX1_ipi_transcendental_of_hl hHL)
    (hpiI ▸ XX1_alg_div hγ halg)

/-- `1` and a transcendental are `Qbar`-independent. -/
theorem XX1_pair_one_transcendental_indep {t : ℂ} (ht : Transcendental ℚ t) :
    LinearIndependent (↥Qbar) ![1, t] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hsmul : ∀ (c : ↥Qbar) (z : ℂ), c • z = (c : ℂ) * z := fun _ _ => rfl
  simp only [hsmul, mul_one] at hab
  by_cases hb : (b : ℂ) = 0
  · rw [hb, zero_mul, add_zero] at hab
    exact ⟨Subtype.ext hab, Subtype.ext hb⟩
  · exfalso
    have ht_eq : t = -((a : ℂ) / (b : ℂ)) := by
      rw [← neg_div, eq_div_iff hb]
      linear_combination hab
    apply ht
    rw [ht_eq]
    exact XX1_alg_neg (XX1_alg_div (mem_Qbar_iff.mp a.2) (mem_Qbar_iff.mp b.2))

/-- The conditional route. -/
theorem XX1_recip_pi_not_log_of_sfe_hl (hS : StrongFourExponentials)
    (hHL : HermiteLindemann) : ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  intro γ hγ hγ0 hexp
  have hpiI0 : ((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero _ Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hsmul : ∀ (c : ↥Qbar) (z : ℂ), c • z = (c : ℂ) * z := fun _ _ => rfl
  have hind1 : LinearIndependent (↥Qbar) ![1, γ / (((Real.pi : ℝ) : ℂ) * Complex.I)] :=
    XX1_pair_one_transcendental_indep
      (XX1_lambda_transcendental_of_hl hHL hγ hγ0)
  have hind2 : LinearIndependent (↥Qbar) ![1, ((Real.pi : ℝ) : ℂ) * Complex.I] :=
    XX1_pair_one_transcendental_indep (XX1_ipi_transcendental_of_hl hHL)
  have hone : (1 : ℂ) ∈ LogAlgTilde := Submodule.subset_span (Set.mem_insert _ _)
  have hlamT : γ / (((Real.pi : ℝ) : ℂ) * Complex.I) ∈ LogAlgTilde :=
    Submodule.subset_span (Set.mem_insert_of_mem _ hexp)
  have hpiiT : ((Real.pi : ℝ) : ℂ) * Complex.I ∈ LogAlgTilde := by
    apply Submodule.subset_span (Set.mem_insert_of_mem _ _)
    show IsAlgebraic ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I))
    rw [Complex.exp_pi_mul_I]
    exact XX1_alg_neg isAlgebraic_one
  have hγT : γ ∈ LogAlgTilde := by
    have h := Submodule.smul_mem LogAlgTilde (⟨γ, mem_Qbar_iff.mpr hγ⟩ : ↥Qbar) hone
    simpa [hsmul] using h
  have hlam_pi : γ / (((Real.pi : ℝ) : ℂ) * Complex.I) *
      (((Real.pi : ℝ) : ℂ) * Complex.I) = γ :=
    div_mul_cancel₀ _ hpiI0
  apply hS 1 _ 1 _ hind1 hind2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hone
  · simpa using hpiiT
  · simpa using hlamT
  · rw [hlam_pi]; exact hγT

end DiazModulus


open DiazModulus in
theorem solution :
    StrongFourExponentials →
      ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
        ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) :=
  fun hS => DiazModulus.XX1_recip_pi_not_log_of_sfe_hl hS DiazModulus.hermite_lindemann_holds
