-- Prove2me | solution 1 for Formalism.DivisionValues.Rb.Qd_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:12.125869+00:00
-- url     : https://prove2.me/submissions/c72826f1-33cd-47aa-8c58-2896a99d79a9

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
import Theorems.Thm_Formalism_DivisionValues_Rb_conjT_map_conj
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
    (φ : K →+* ℂ) : Qd P H (ComplexEmbedding.conjugate φ) = starRingEnd ℂ (Qd P H φ) := by
  have hP : P.map (ComplexEmbedding.conjugate φ) = (P.map φ).map (starRingEnd ℂ) := by
    ext i j; simp [ComplexEmbedding.conjugate_coe_eq]
  have hH : H.map (ComplexEmbedding.conjugate φ) = (H.map φ).map (starRingEnd ℂ) := by
    ext i j; simp [ComplexEmbedding.conjugate_coe_eq]
  unfold Qd
  rw [hP, hH, ← R0.map_inv_field, conjT_map_conj, ← Matrix.map_mul, ← Matrix.map_mul,
    RingHom.map_det, RingHom.mapMatrix_apply]
end Formalism.DivisionValues.Rb
