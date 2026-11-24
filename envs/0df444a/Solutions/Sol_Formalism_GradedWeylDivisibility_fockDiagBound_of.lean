-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.fockDiagBound_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:00.913936+00:00
-- url     : https://prove2.me/submissions/16b92845-1b0b-43df-a03b-389cbca3e3ce

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockDiagBound
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_coeff_rowAct_diag
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_term
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_term0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Finset
noncomputable section
namespace Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)
private theorem mul_sq_mul_le_sq_mul_mul_of_le {c N p q : ℝ} (hc : 0 ≤ c) (hN : 0 ≤ N) (hp : 0 ≤ p)
    (hpq : p ≤ q) : c * p ^ 2 * N ≤ q ^ 2 * (c * N) := by
  have h1 : p * p ≤ q * q := mul_self_le_mul_self hp hpq
  have h2 : 0 ≤ c * N := mul_nonneg hc hN
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  calc c * p ^ 2 * N = (p * p) * (c * N) := by ring
    _ ≤ (q * q) * (c * N) := h3
    _ = q ^ 2 * (c * N) := by ring
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (h : DomPow) : FockDiagBound := by
  unfold DomPow at h
  unfold FockDiagBound
  intro r n t lam ht0 ht f hdom hsum
  have hcoeff : ∀ m, coeff m (rowAct ℂ (Matrix.diagonal fun a => (t a : ℂ)) f) =
      coeff m f * ((∏ a : Fin r, t a ^ rowDeg m a : ℝ) : ℂ) := by
    intro m
    simp only [ldiag_coeff_rowAct_diag, Complex.ofReal_prod, Complex.ofReal_pow]
  have hsupp : (rowAct ℂ (Matrix.diagonal fun a => (t a : ℂ)) f).support ⊆ f.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [hcoeff, h0, zero_mul])
  have hq : ∏ a : Fin r, t a ^ (2 * lam a) = (∏ a : Fin r, t a ^ lam a) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← pow_mul, Nat.mul_comm]
  rw [Formalism.REAL.fischerInner_eq_sum_of_subset _ _ _ hsupp,
    Formalism.REAL.fischerInner_eq_sum_of_subset f f f.support (Finset.Subset.refl _)]
  simp only [hcoeff, ldiag_term]
  simp only [ldiag_term0, Complex.re_sum, Complex.ofReal_re]
  rw [hq, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  have hP0 : 0 ≤ ∏ a : Fin r, t a ^ rowDeg m a :=
    Finset.prod_nonneg fun a _ => pow_nonneg (ht0 a) _
  have hPle := h r t (rowDeg m) lam ht0 ht (hdom m hm) (hsum m hm)
  exact mul_sq_mul_le_sq_mul_mul_of_le (Complex.normSq_nonneg _) (Nat.cast_nonneg _) hP0 hPle
end Formalism.GradedWeylDivisibility
