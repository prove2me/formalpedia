-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.constantCoeff_oddDerivative_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:46.272034+00:00
-- url     : https://prove2.me/submissions/0f8e7c10-cd11-491a-993d-fe6501d00ca8

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmS_cc_subst

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [Field K] {d : ℕ} [NeZero d] {be : MvPowerSeries (ZMod d) K}
    (hbe0 : constantCoeff be = 0) : constantCoeff (de2 be) = 0 := by
  have c0 : constantCoeff (subst (s0 (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp [s0])
  have c1 : constantCoeff (subst (s1' (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp only [s1']; split_ifs <;> simp)
  have c2 : constantCoeff (subst (s2' (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp only [s2']; split_ifs <;> simp)
  simp only [de2, map_sub, c0, c1, c2, sub_zero]
end Formalism.DworkPowerSeriesWeights
