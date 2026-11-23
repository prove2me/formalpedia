-- Prove2me | solution 1 for Formalism.DivisionValues.R0.conjTranspose_eq_of_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:17.484807+00:00
-- url     : https://prove2.me/submissions/95dacabb-fcab-4be2-a241-69ed4b7268b7

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef
import Theorems.Thm_Formalism_DivisionValues_R0_conjTranspose_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.R0
variable {K : Type} [Field K] [StarRing K]
namespace Formalism.DivisionValues.R0
theorem _root_.solution [NumberField K] (v0 : InfinitePlace K) (hv0 : IsConjAt v0)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : (H.map v0.embedding).PosDef) : Hᴴ = H := by
  have h1 := conjTranspose_map v0.embedding hv0 H
  have h2 : (H.map v0.embedding)ᴴ = H.map v0.embedding := hH.isHermitian
  ext i j
  have h3 := congrFun (congrFun (h1.trans h2) i) j
  simp only [Matrix.map_apply] at h3
  exact v0.embedding.injective h3
end Formalism.DivisionValues.R0
