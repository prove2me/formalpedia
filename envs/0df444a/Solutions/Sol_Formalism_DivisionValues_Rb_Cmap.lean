-- Prove2me | solution 1 for Formalism.DivisionValues.Rb.Cmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:46.163043+00:00
-- url     : https://prove2.me/submissions/e89dc277-bb01-488a-8bf4-8ef1e9e0579f

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DeterminantCauchySchwarz
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaSecond
import Theorems.Thm_Formalism_DivisionValues_Rb_tw_apply
import Theorems.Thm_Formalism_DivisionValues_R0_map_inv_field


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
open Formalism.DivisionValues.Rb
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.Rb
theorem _root_.solution {n D : ℕ} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K)
    (φ : K →+* ℂ) :
    (P * H⁻¹ * Pᴴ).map φ = (P.map φ) * (H.map φ)⁻¹ * (P.map (tw φ))ᴴ := by
  rw [Matrix.map_mul, Matrix.map_mul, R0.map_inv_field]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply, tw_apply]
end Formalism.DivisionValues.Rb
