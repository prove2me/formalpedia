-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.ctr_h
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:35.103021+00:00
-- url     : https://prove2.me/submissions/cbdd8a77-3f6d-4693-9946-59da2b4823c9

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrF_apply
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_pderiv_inr_h
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_pderiv_inl_h
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_euler_X_sum
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_euler_y

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ctrF K k (hXY K k * f) = hXY K k * ctrF K k f + ((A + B + k : ℕ) : K) • f := by
  rw [ctrF_apply, ctrF_apply]
  have e : ∀ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) (hXY K k * f)) =
      f + X (Sum.inl i) * pderiv (Sum.inl i) f + X (Sum.inr i) * pderiv (Sum.inr i) f +
        hXY K k * pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := by
    intro i
    simp only [Derivation.leibniz, map_add, pderiv_inr_h, pderiv_inl_h, pderiv_X_self, smul_eq_mul]
    ring
  simp only [e, Finset.sum_add_distrib, euler_X_sum hf, euler_y hf, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, MvPolynomial.smul_eq_C_mul, map_natCast]
  push_cast
  ring
end Formalism.CountingSumsFrames.Har2
