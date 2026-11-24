-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.sum_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:06.213155+00:00
-- url     : https://prove2.me/submissions/a0b2c7a0-e54c-4676-9981-56aafdf22c08

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
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
theorem _root_.solution (p : ℕ) (Z Y : MvPowerSeries (Tp ⊕ Lw) K) (aA : Φ → K) (dA : Φ → Tp →₀ ℕ)
    (aB : κ → K) (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K) :
    ∑ j, piece p Z Y aA dA aB dB b j =
      ∑ φ, MvPowerSeries.C (aA φ) * topMonoS (Lw := Lw) (dA φ) +
        ∑ k, MvPowerSeries.C (aB k) * topMonoS (dB k) * lowLin (b k) + Z +
        MvPowerSeries.C (p : K) * Y := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [piece, Sum.elim_inl, Sum.elim_inr, if_true, one_ne_zero, if_false]
  ring
end Formalism.InvariantFactorPaths.G7.ETerm
