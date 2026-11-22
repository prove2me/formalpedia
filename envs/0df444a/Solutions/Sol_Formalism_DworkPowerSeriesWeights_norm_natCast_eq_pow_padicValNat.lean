-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:17.060203+00:00
-- url     : https://prove2.me/submissions/54f89d51-5d55-44f5-b526-27881e325be0

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormNatCastEqOneOfNotDvd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_one_of_not_dvd
import Theorems.Thm_GlobalTheory_NatCastUnitNorm_norm_natCast_eq_one_of_not_dvd


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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {l n : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1)
    (hn : n ≠ 0) : ‖(n : K)‖ = ‖(l : K)‖ ^ padicValNat l n := by
  have hfac := Nat.ordProj_mul_ordCompl_eq_self n l
  have hnd := Nat.not_dvd_ordCompl hl hn
  rw [Nat.factorization_def n hl] at hfac hnd
  conv_lhs => rw [← hfac]
  rw [Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow, norm_natCast_eq_one_of_not_dvd hl hlt hnd,
    mul_one]
end Formalism.DworkPowerSeriesWeights
