-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jet_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:33.546991+00:00
-- url     : https://prove2.me/submissions/6c8d65ad-e0ba-4b4c-8a36-f006081c105c

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_mul_linForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_quadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_linSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_linSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_quadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_prod_lin_mul
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_mvExp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_add_right


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
variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {α : Type} [DecidableEq α] (c : ι → ι → K) (S : K) (L : α → ι → K) (a : α)
    (s : Finset α) (ha : a ∉ s) (h : MvPowerSeries ι K) :
    jetPair (∏ i ∈ insert a s, linForm (L i)) (mvExp ((-S) • quadSer c) * h) =
      jetPair (∏ i ∈ s, linForm (L i)) (mvExp ((-S) • quadSer c) * dirD (L a) h) +
        ∑ b ∈ s, (-S * polar c (L a) (L b)) *
          jetPair (∏ i ∈ s.erase b, linForm (L i)) (mvExp ((-S) • quadSer c) * h) := by
  have h0 : MvPowerSeries.constantCoeff ((-S) • quadSer c) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, constantCoeff_quadSer, mul_zero]
  rw [Finset.prod_insert ha, mul_comm, jetPair_mul_linForm, Derivation.leibniz, dirD_mvExp _ _ h0,
    Derivation.map_smul, dirD_quadSer, smul_eq_mul, smul_eq_mul, jetPair_add_right]
  congr 1
  rw [show h * ((-S) • linSer c (L a) * mvExp ((-S) • quadSer c)) =
      MvPowerSeries.C (-S) * (linSer c (L a) * (mvExp ((-S) • quadSer c) * h)) by
    rw [MvPowerSeries.smul_eq_C_mul]; ring]
  rw [jetPair_C_mul_right, jetPair_prod_lin_mul L (linSer c (L a)) (fun b => polar c (L a) (L b))
    (constantCoeff_linSer _ _) (fun b => dirD_linSer _ _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring
end Formalism.DworkPowerSeriesWeights
