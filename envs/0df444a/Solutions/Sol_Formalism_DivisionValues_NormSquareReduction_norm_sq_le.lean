-- Prove2me | solution 1 for Formalism.DivisionValues.NormSquareReduction.norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:16.602298+00:00
-- url     : https://prove2.me/submissions/ac94a2f9-a42c-4464-84ab-ea8643449d5c

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementACE
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.NormSquareReduction
variable {Q E : Type} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace Formalism.DivisionValues.NormSquareReduction
theorem _root_.solution (ι : Q →ₗ[ℂ] E) {Ix : Type} [Fintype Ix] (Qp : Ix → Submodule ℂ Q)
    (hsup : (⨆ p, Qp p) = ⊤) (s : Ix → ℝ) (smin : ℝ) (hs : ∀ p, smin ≤ s p)
    (hι : ∀ p, ∀ x ∈ Qp p, ∀ y : Q, ⟪ι x, ι y⟫_ℂ = (s p : ℂ) * ⟪x, y⟫_ℂ) (F : Q) :
    smin * ‖F‖ ^ 2 ≤ ‖ι F‖ ^ 2 := by
  classical
  have hF : F ∈ ⨆ p, Qp p := by rw [hsup]; exact Submodule.mem_top

  obtain ⟨y, hy, hFy⟩ : ∃ y : Ix → Q, (∀ p, y p ∈ Qp p) ∧ F = ∑ p, y p := by
    refine Submodule.iSup_induction
      (motive := fun z => ∃ y : Ix → Q, (∀ p, y p ∈ Qp p) ∧ z = ∑ p, y p) Qp hF ?_ ?_ ?_
    · intro i x hx
      refine ⟨Pi.single i x, fun p => ?_, ?_⟩
      · rcases eq_or_ne p i with rfl | h
        · simpa using hx
        · rw [Pi.single_eq_of_ne h]; exact (Qp p).zero_mem
      · rw [Finset.sum_pi_single']; simp
    · exact ⟨0, fun p => (Qp p).zero_mem, by simp⟩
    · rintro x1 x2 ⟨y1, hy1, h1⟩ ⟨y2, hy2, h2⟩
      refine ⟨y1 + y2, fun p => (Qp p).add_mem (hy1 p) (hy2 p), ?_⟩
      rw [h1, h2]; simp [Finset.sum_add_distrib]

  have horth : ∀ p q, s p ≠ s q → ⟪y p, y q⟫_ℂ = 0 := by
    intro p q hpq
    have h1 := hι p (y p) (hy p) (y q)
    have h2 := hι q (y q) (hy q) (y p)
    have h3 : ⟪ι (y p), ι (y q)⟫_ℂ = (s q : ℂ) * ⟪y p, y q⟫_ℂ := by
      rw [← inner_conj_symm, h2, map_mul, Complex.conj_ofReal, inner_conj_symm]
    have h4 : ((s p : ℂ) - (s q : ℂ)) * ⟪y p, y q⟫_ℂ = 0 := by
      rw [sub_mul, ← h1, ← h3, sub_self]
    have h5 : (s p : ℂ) - (s q : ℂ) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hpq
    exact (mul_eq_zero.mp h4).resolve_left h5

  have hkey : ∀ p q, ⟪ι (y p), ι (y q)⟫_ℂ - (smin : ℂ) * ⟪y p, y q⟫_ℂ =
      ⟪((Real.sqrt (s p - smin) : ℝ) : ℂ) • y p, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • y q⟫_ℂ := by
    intro p q
    rw [hι p (y p) (hy p) (y q), inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      ← sub_mul, ← mul_assoc]
    by_cases hpq : s p = s q
    · congr 1
      have hc : Real.sqrt (s p - smin) * Real.sqrt (s q - smin) = s p - smin := by
        rw [hpq, Real.mul_self_sqrt (by linarith [hs q])]
      rw [← Complex.ofReal_mul, hc, Complex.ofReal_sub]
    · simp [horth p q hpq]
  have hsum : ⟪ι F, ι F⟫_ℂ - (smin : ℂ) * ⟪F, F⟫_ℂ =
      ⟪∑ p, ((Real.sqrt (s p - smin) : ℝ) : ℂ) • y p,
        ∑ p, ((Real.sqrt (s p - smin) : ℝ) : ℂ) • y p⟫_ℂ := by
    simp only [hFy, map_sum, sum_inner, inner_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    first
      | exact hkey a b
      | exact hkey b a
  obtain ⟨Z, hZ⟩ : ∃ Z : Q, ⟪ι F, ι F⟫_ℂ - (smin : ℂ) * ⟪F, F⟫_ℂ = ⟪Z, Z⟫_ℂ := ⟨_, hsum⟩
  have hn : ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] (x : G),
      (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
    intro G _ _ x
    first
      | exact inner_self_eq_norm_sq (𝕜 := ℂ) x
      | exact (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
      | simp
  have hre := congrArg Complex.re hZ
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hre
  rw [hn, hn, hn] at hre
  nlinarith [sq_nonneg ‖Z‖]
end Formalism.DivisionValues.NormSquareReduction
