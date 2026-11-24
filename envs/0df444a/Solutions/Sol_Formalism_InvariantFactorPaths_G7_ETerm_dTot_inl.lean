-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.dTot_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:56.488842+00:00
-- url     : https://prove2.me/submissions/db725689-227e-49e7-85e4-71a90f1c63e3

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_mapDomain_inl_inl
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
variable {K Tp Lw Φ κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype Tp] [Fintype Lw]
  [Fintype Φ] [Fintype κ]
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution (dA : Φ → Tp →₀ ℕ) (dB : κ → Tp →₀ ℕ) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) (τ : Tp) :
    dTot (Lw := Lw) dA dB k (Sum.inl τ) =
      ∑ φ, k (Sum.inl φ) * dA φ τ + ∑ x, k (Sum.inr (Sum.inl x)) * dB x τ := by
  simp [dTot, mapDomain_inl_inl]
end Formalism.InvariantFactorPaths.G7.ETerm
