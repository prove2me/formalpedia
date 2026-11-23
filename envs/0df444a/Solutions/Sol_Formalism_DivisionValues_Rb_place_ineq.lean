-- Prove2me | solution 1 for Formalism.DivisionValues.Rb.place_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:50.042008+00:00
-- url     : https://prove2.me/submissions/57e21111-9cac-4a64-9255-554581d9939e

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
import Theorems.Thm_Formalism_DivisionValues_Rb_Qd_re_mk
import Theorems.Thm_Formalism_DivisionValues_Rb_Cmap
import Theorems.Thm_Formalism_DivisionValues_Rb_Hmap_tw
import Theorems.Thm_Formalism_DivisionValues_Rb_Qd_place_re

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
theorem _root_.solution (hCS : DetCS) (K0 : Subfield K) (hK0 : IsCMSub K0) {n D : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (hH : ∀ i j, H i j ∈ K0)
    (hHpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef)
    (P : Matrix (Fin D) (Fin n) K) (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hXQ : IsQuotMetric P H XQ) (hc : (P * H⁻¹ * Pᴴ).det ≠ 0) (v : InfinitePlace K) :
    (metMat XQ v).det.re * (metMat XQ (plc v)).det.re ≤
      (‖v.embedding (P * H⁻¹ * Pᴴ).det‖ ^ 2)⁻¹ := by
  have hS : ((H.map v.embedding)⁻¹).PosDef := (hHpos v).inv
  have h := hCS n D _ hS (P.map v.embedding) (P.map (tw v.embedding))
  have e1 : v.embedding (P * H⁻¹ * Pᴴ).det =
      (P.map v.embedding * (H.map v.embedding)⁻¹ * (P.map (tw v.embedding))ᴴ).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Cmap]
  have e2 : (P.map v.embedding * (H.map v.embedding)⁻¹ * (P.map v.embedding)ᴴ).det.re =
      ((metMat XQ v).det.re)⁻¹ := (Qd_place_re P H XQ hXQ v).1
  have e3 : (P.map (tw v.embedding) * (H.map v.embedding)⁻¹ * (P.map (tw v.embedding))ᴴ).det.re =
      ((metMat XQ (plc v)).det.re)⁻¹ := by
    rw [← Hmap_tw K0 hK0 H hH v.embedding, ← (Qd_place_re P H XQ hXQ (plc v)).1]
    exact (Qd_re_mk P H (tw v.embedding)).symm
  rw [← e1, e2, e3, ← mul_inv] at h
  have hr := (Qd_place_re P H XQ hXQ v).2
  have hr' := (Qd_place_re P H XQ hXQ (plc v)).2
  have ha : 0 < ‖v.embedding (P * H⁻¹ * Pᴴ).det‖ ^ 2 := by
    have : v.embedding (P * H⁻¹ * Pᴴ).det ≠ 0 := (map_ne_zero _).mpr hc
    positivity
  exact (le_inv_comm₀ ha (mul_pos hr hr')).mp h
end Formalism.DivisionValues.Rb
