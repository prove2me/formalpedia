-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.sq_comb_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:31.34515+00:00
-- url     : https://prove2.me/submissions/e7a17c00-aba2-4857-97fd-d7c8a03d89c2

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a)
    (D : ℕ → Fn B A') (M : ℕ) (k : ℕ → B.Ω → ℝ) (K : ℝ) (hK : ∀ p ∈ range (M+1), ∀ ω, |k p ω| ≤ K) (ω : B.Ω) :
    LE.sq B wt (fun ω a => ∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial) ω ≤
      (M + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (D p) ω := by
  unfold LE.sq
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.mul_sum]
  have h1 : ‖∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial‖ ≤ ∑ p ∈ range (M+1), K * ‖D p ω a‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    have hf : (1:ℝ) ≤ p.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr p.factorial_ne_zero
    calc |k p ω| * ‖D p ω a‖ / p.factorial ≤ |k p ω| * ‖D p ω a‖ := div_le_self (by positivity) hf
      _ ≤ K * ‖D p ω a‖ := mul_le_mul_of_nonneg_right (hK p hp ω) (norm_nonneg _)
  have h2 : (∑ p ∈ range (M+1), K * ‖D p ω a‖) ^ 2 ≤ (M + 1) * ∑ p ∈ range (M+1), (K * ‖D p ω a‖) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range (M+1)) (f := fun p => K * ‖D p ω a‖)
    simpa using this
  have h3 : ‖∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial‖ ^ 2 ≤
      (M + 1) * K ^ 2 * ∑ p ∈ range (M+1), ‖D p ω a‖ ^ 2 := by
    calc _ ≤ (∑ p ∈ range (M+1), K * ‖D p ω a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ = _ := by simp_rw [mul_pow]; rw [← Finset.mul_sum]; ring
  calc wt ω a * _ ≤ wt ω a * ((M + 1) * K ^ 2 * ∑ p ∈ range (M+1), ‖D p ω a‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (hpos ω a)
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.LEx1
