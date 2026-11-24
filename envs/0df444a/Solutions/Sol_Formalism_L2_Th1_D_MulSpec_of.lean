-- Prove2me | solution 1 for Formalism.L2.Th1.D.MulSpec_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:13.419899+00:00
-- url     : https://prove2.me/submissions/23e196c3-ef43-4c2c-ad8b-c1afcb516cee

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExponentialSpecification
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_inj
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_ip_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_coeff_one_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_constantCoeff_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_funEq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_subst_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_rescale_lgF


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
theorem _root_.solution : ExpSpec → IPLemma → IPClosure → MulSpec := by
  intro hE hL hC K _ _ _ l σ hU c
  have hp : l.Prime := hU.1
  have hl : 2 ≤ l := hp.two_le
  have hlK : (l : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨hc, h1, _, _⟩ := hE K l hl
  have h0 := constantCoeff_lgF (K := K) l hl
  have huniq : ∀ e e' : PowerSeries K, IsMul l c e → IsMul l c e' → e = e' := fun e e' he he' =>
    inj l hl e e' he.1 he'.1 (he.2.trans he'.2.symm)
  refine ⟨?_, huniq, ?_⟩
  · have hg0 : PowerSeries.constantCoeff (PowerSeries.C c * lgF K l) = 0 := by
      rw [map_mul, h0, mul_zero]
    refine ⟨PowerSeries.subst (PowerSeries.C c * lgF K l) (expF K l),
      PowerSeries.constantCoeff_subst_eq_zero hg0 _ hc, ?_⟩
    rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hc)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hg0), h1,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hg0)]
  · intro hc1 hσc e he n
    have hip : IP l σ (MvPowerSeries.C c * (lgF K l : MvPowerSeries Unit K)) :=
      (hC K l σ Unit).2.2 c _ hc1 hσc (ip_lgF l σ hl hlK)
    obtain ⟨h, hh0, hhI, hh⟩ := hL K l σ hU Unit _ hip
    have : e = h := huniq e h he ⟨hh0, hh⟩
    rw [this]
    exact hhI (Finsupp.single () n)
end Formalism.L2.Th1.D
