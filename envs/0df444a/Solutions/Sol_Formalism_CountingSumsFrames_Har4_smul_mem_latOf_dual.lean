-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.smul_mem_latOf_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:14.927899+00:00
-- url     : https://prove2.me/submissions/5e0a1dac-1992-4485-9ea4-8cc2041d9804

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds

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
open Formalism.CountingSumsFrames.Har4
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution (R : Subring K) (g : GL (Fin k) K) {r : K} (hr : r ∈ R) {f : PolXY K k}
    (hf : f ∈ latOf g (DualLat R)) : r • f ∈ latOf g (DualLat R) := by
  obtain ⟨h, hh, rfl⟩ := hf
  have hh' : ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m h ∈ R := hh
  refine ⟨r • h, ?_, by rw [map_smul]⟩
  show ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m (r • h) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_left_comm]
  exact R.mul_mem hr (hh' m)
end Formalism.CountingSumsFrames.Har4
