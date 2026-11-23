-- Prove2me | solution 1 for Formalism.DivisionValues.Rb.Qd_re_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:19.889862+00:00
-- url     : https://prove2.me/submissions/d0f505d9-150b-45ef-8c5c-7cd87b346453

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
import Theorems.Thm_Formalism_DivisionValues_Rb_Qd_conjugate

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
    (φ : K →+* ℂ) : (Qd P H (InfinitePlace.mk φ).embedding).re = (Qd P H φ).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, Qd_conjugate, Complex.conj_re]
end Formalism.DivisionValues.Rb
