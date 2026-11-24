-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.hasseDir_topLow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:08.667502+00:00
-- url     : https://prove2.me/submissions/56aad4aa-8461-442a-8900-4ccfbed10790

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_shiftPoly_topMonoP
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_shiftPoly_lowPoly
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right


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
open Formalism.InvariantFactorPaths.G7.ETerm
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact jetPair_eq_sum jetPair_C_mul_right jetPair_sum_right)
variable {K Tp Lw : Type} [Field K]
variable {κ : Type} [Fintype κ]
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution (b : κ → Lw → K) (β : κ →₀ ℕ) (e : Tp →₀ ℕ) (Q : MvPolynomial Lw K) :
    hasseDir (ext0 (Tp := Tp) b) β (topMonoP e * lowPoly Q) =
      topMonoP e * lowPoly (hasseDir b β Q) := by
  have hm : shiftPoly (ext0 (Tp := Tp) b) (topMonoP e * lowPoly Q) =
      shiftPoly (ext0 (Tp := Tp) b) (topMonoP e) * shiftPoly (ext0 (Tp := Tp) b) (lowPoly Q) := by
    unfold shiftPoly
    exact map_mul _ _ _
  unfold hasseDir
  rw [hm, shiftPoly_topMonoP, shiftPoly_lowPoly, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  rfl
end Formalism.InvariantFactorPaths.G7.ETerm
