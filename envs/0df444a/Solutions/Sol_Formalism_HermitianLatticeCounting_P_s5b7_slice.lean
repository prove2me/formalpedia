-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_slice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:54.166144+00:00
-- url     : https://prove2.me/submissions/ee1d783b-424e-43e2-9f9e-f8e8b6cfa73b

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_gram_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (R : ℝ) (d r : ℕ) (t : ℝ) (x : EuclideanSpace ℂ (Fin (d + 1))) (hx : x ≠ 0)
    (Φ : EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℂ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)))
    (hΦ : Φ (((‖x‖⁻¹ : ℝ) : ℂ) • x) = WithLp.toLp 2 (1, 0))
    (a' : Fin r → EuclideanSpace ℂ (Fin (d + 1)))
    (h : (Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1))) ∈ s5b7_A R (d + 1) (r + 1) t) :
    (∀ b, ‖(Φ (a' b)).ofLp.1‖ ≤ R) ∧ (fun b => (Φ (a' b)).ofLp.2) ∈ s5b7_A R d r (t / ‖x‖) := by
  obtain ⟨hn, hg⟩ := h
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxc : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hnb : ∀ b, ‖a' b‖ ≤ R := fun b => by simpa using hn b.succ
  have hsq : ∀ b, ‖(Φ (a' b)).ofLp.1‖ ^ 2 + ‖(Φ (a' b)).ofLp.2‖ ^ 2 = ‖a' b‖ ^ 2 := by
    intro b
    rw [← Φ.norm_map (a' b), WithLp.prod_norm_sq_eq_of_L2]
    rfl
  have hR0 : ∀ b, 0 ≤ ‖a' b‖ := fun b => norm_nonneg _
  have hΦx : Φ x = ((‖x‖ : ℝ) : ℂ) • WithLp.toLp 2 ((1 : ℂ), (0 : EuclideanSpace ℂ (Fin d))) := by
    rw [← hΦ, map_smul, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ hxc, one_smul]
  refine ⟨fun b => ?_, fun b => ?_, ?_⟩
  · refine le_trans ?_ (hnb b)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by nlinarith [hsq b, sq_nonneg ‖(Φ (a' b)).ofLp.2‖])
  · refine le_trans ?_ (hnb b)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by nlinarith [hsq b, sq_nonneg ‖(Φ (a' b)).ofLp.1‖])
  · have hgram : (Matrix.gram ℂ (Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1)))).det =
        (((‖x‖ : ℝ) : ℂ) ^ 2) * (Matrix.gram ℂ (fun b => (Φ (a' b)).ofLp.2)).det := by
      have e1 : Matrix.gram ℂ (Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1))) =
          Matrix.gram ℂ (fun i => Φ ((Fin.cons x a' : Fin (r + 1) → _) i)) := by
        ext i j
        simp only [Matrix.gram_apply, Φ.inner_map_map]
      have e2 : (fun i => Φ ((Fin.cons x a' : Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1))) i)) =
          Fin.cons (Φ x) (fun b => ((Φ (a' b)).ofLp.1 / ((‖x‖ : ℝ) : ℂ)) • Φ x +
            WithLp.toLp 2 ((0 : ℂ), (Φ (a' b)).ofLp.2)) := by
        funext i
        refine Fin.cases ?_ (fun b => ?_) i
        · simp
        · simp only [Fin.cons_succ]
          rw [hΦx, smul_smul, div_mul_cancel₀ _ hxc]
          apply WithLp.ofLp_injective 2
          apply Prod.ext <;> simp
      rw [e1, e2, s5b7_gram_cons]
      · rw [Φ.norm_map]
        congr 2
        ext i j
        simp [Matrix.gram_apply, WithLp.prod_inner_apply]
      · intro b
        rw [hΦx]
        simp [WithLp.prod_inner_apply]
    rw [hgram, norm_mul, norm_pow, Complex.norm_real, norm_norm, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hx0.le] at hg
    rw [le_div_iff₀ hx0]
    linarith
end Formalism.HermitianLatticeCounting.P
