-- Prove2me | solution 1 for Formalism.L2.Th1.D.teichmuller_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:52:52.464667+00:00
-- url     : https://prove2.me/submissions/d2f620b6-a78e-4a7d-b21d-7e7a19cc3448

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExponentialSpecification
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_norm_eq_one_of_pow
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_root_eq_of_norm_lt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_one_of_not_dvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_coeff_one_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_constantCoeff_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_funEq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_subst_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_rescale_lgF
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws (constantCoeff_lgF coeff_one_lgF lgF_subst_inj lgF_funEq map_lgF
  rescale_lgF)
open FormalExponential
namespace Formalism.L2.Th1.D
theorem _root_.solution : TeichSigma := by
  intro K _ _ _ l d σ hU hd ζ hζ
  obtain ⟨hp, _, hnl, _, hσ⟩ := hU
  have hlt : ‖(l : K)‖ < 1 := by
    rw [hnl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hpos : 1 ≤ l ^ d := Nat.one_le_pow _ _ hp.pos
  have hnd : ¬ l ∣ l ^ d - 1 := by
    intro h
    have h1 : l ∣ l ^ d := dvd_pow_self l (by omega)
    have h2 : l ∣ 1 := by
      have := (Nat.dvd_sub h1 h)
      rwa [Nat.sub_sub_self hpos] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hN : ‖((l ^ d - 1 : ℕ) : K)‖ = 1 := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp hlt hnd
  have hN0 : l ^ d - 1 ≠ 0 := by
    intro h
    rw [h] at hnd
    exact hnd (dvd_zero l)
  have nζ : ‖ζ‖ = 1 := norm_eq_one_of_pow hN0 hζ
  refine root_eq_of_norm_lt hN ?_ ?_ ?_
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  · refine lt_of_le_of_lt (hσ ζ nζ.le) ?_
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
end Formalism.L2.Th1.D
