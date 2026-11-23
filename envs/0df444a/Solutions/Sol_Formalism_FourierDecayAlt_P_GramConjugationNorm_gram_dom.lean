-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramConjugationNorm.gram_dom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:01.004073+00:00
-- url     : https://prove2.me/submissions/505043be-c245-4258-833b-754b46e041b5

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramConjugationNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_gram_re_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramConjugationNorm
open Finset Filter Topology Formalism.FourierDecayAlt.TA
open scoped InnerProductSpace ComplexConjugate
variable {E : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.GramConjugationNorm
theorem _root_.solution {ι : Type} (R : Finset ι) (c : ℝ) (k : Pt E → Pt E → ℂ)
    (T : ι → Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E))
    (hk : PSDOn P (fun h h' => (c : ℂ) * k h h' - ∑ t ∈ R, T t h h')) :
    ∑ t ∈ R, (gram (T t) V P).re ≤ c * (gram k V P).re := by
  have h0 := gram_re_nonneg _ V P hk
  have h1 : gram (fun h h' => (c : ℂ) * k h h' - ∑ t ∈ R, T t h h') V P =
      (c : ℂ) * gram k V P - ∑ t ∈ R, gram (T t) V P := by
    unfold gram
    have h2 : ∑ t ∈ R, ∑ p ∈ P, ∑ p' ∈ P, T t p p' * ⟪V p, V p'⟫_ℂ =
        ∑ p ∈ P, ∑ p' ∈ P, ∑ t ∈ R, T t p p' * ⟪V p, V p'⟫_ℂ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
    rw [h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [sub_mul, Finset.sum_mul, mul_assoc]
  rw [h1, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_sum] at h0
  linarith
end Formalism.FourierDecayAlt.P.GramConjugationNorm
