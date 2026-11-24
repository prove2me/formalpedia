-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ext_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:59.975209+00:00
-- url     : https://prove2.me/submissions/f2565bda-686b-4ed9-a054-9631c8d6e52d

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_monomial_eq_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (m : σ →₀ ℕ) (a : K) :
    ext fs φ (monomial m a) = a • (φ (monomial (frst fs m) 1) * monomial (ltr fs m) 1) := by
  rw [monomial_eq_basis, map_smul]
  unfold Formalism.CountingSumsFrames.ext
  rw [Module.Basis.constr_basis]
end Formalism.CountingSumsFrames
