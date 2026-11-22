-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.smul_mem_latOf_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:20.810311+00:00
-- url     : https://prove2.me/submissions/67d78496-af66-4c17-a3c8-53ad59693564

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
    (hf : f ∈ latOf g (GaussLat R)) : r • f ∈ latOf g (GaussLat R) := by
  obtain ⟨h, hh, rfl⟩ := hf
  have hh' : ∀ m, coeff m h ∈ R := hh
  refine ⟨r • h, ?_, by rw [map_smul]⟩
  show ∀ m, coeff m (r • h) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact R.mul_mem hr (hh' m)
end Formalism.CountingSumsFrames.Har4
