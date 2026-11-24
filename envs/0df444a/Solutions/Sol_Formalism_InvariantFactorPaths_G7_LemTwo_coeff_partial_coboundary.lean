-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.coeff_partial_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:01:33.691968+00:00
-- url     : https://prove2.me/submissions/c4a78b06-00cf-4d24-83d6-511fb31f9930

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_include_three_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_subst_slice

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemTwo
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (G : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (m : ℕ) :
    MvPowerSeries.coeff (ext3 e m) (d1 F G) = MvPowerSeries.coeff e (cob F (sl G m)) := by
  have h0 := coeff_subst_slice (f := (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
    (MvPowerSeries.constantCoeff_X 0) G e m
  have h1 := coeff_subst_slice (f := (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K))
    (MvPowerSeries.constantCoeff_X 1) G e m
  rw [include_three_X] at h0 h1
  rw [d1, map_sub, map_sub, coeff_subst_slice hF, cob, map_sub, map_sub, at1, at1]
  rw [← h0, ← h1]
  rfl
end Formalism.InvariantFactorPaths.G7.LemTwo
