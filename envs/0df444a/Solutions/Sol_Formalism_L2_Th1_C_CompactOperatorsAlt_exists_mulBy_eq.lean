-- Prove2me | solution 1 for Formalism.L2.Th1.C.CompactOperatorsAlt.exists_mulBy_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:33:44.842868+00:00
-- url     : https://prove2.me/submissions/dbebcd83-78b1-4c9b-89b2-4f1a3cab994f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_coeff_subst_congr
import Theorems.Thm_Formalism_L2_Th1_C_Pts_coeff_one_linv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_Pts_hasSubst


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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.CompactOperatorsAlt
variable {K : Type} [Field K] {R : Subring K}
namespace Formalism.L2.Th1.C.CompactOperatorsAlt
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) {al : K} (hal : al ≠ 0) :
    ∃ g : PowerSeries K, constantCoeff g = 1 ∧ mulBy l linv al = C al * X * g := by
  have ha0 : constantCoeff (C al * l) = 0 := by rw [map_mul, h.1, mul_zero]
  have hv0 : coeff 0 (mulBy l linv al) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]
    exact Pts.constantCoeff_mulBy h al
  have hv1 : coeff 1 (mulBy l linv al) = al := by
    have hc := IntegralMvPolynomialLemmas.coeff_subst_congr (g := linv) (h := (X : PowerSeries K)) (a := C al * l) ha0
      (Finsupp.single () 1) (fun k hk => by
        rw [Finsupp.degree_single] at hk
        interval_cases k
        · simp [h.2.2.1]
        · rw [Pts.coeff_one_linv h, coeff_one_X])
    rw [PowerSeries.subst_X (Pts.hasSubst ha0)] at hc
    have h1 : coeff 1 (mulBy l linv al) = coeff 1 (C al * l) := hc
    rw [h1, coeff_C_mul, h.2.1, mul_one]
  refine ⟨PowerSeries.mk fun n => al⁻¹ * coeff (n + 1) (mulBy l linv al), ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add, hv1, inv_mul_cancel₀ hal]
  · have hr : ∀ g : PowerSeries K, C al * X * g = X * (C al * g) := fun g => by ring
    rw [hr]
    ext n
    cases n with
    | zero => rw [coeff_zero_X_mul, hv0]
    | succ n => rw [coeff_succ_X_mul, coeff_C_mul, coeff_mk, mul_inv_cancel_left₀ hal]
end Formalism.L2.Th1.C.CompactOperatorsAlt
