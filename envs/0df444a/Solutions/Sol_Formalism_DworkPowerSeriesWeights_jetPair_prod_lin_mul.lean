-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_prod_lin_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:41.9202+00:00
-- url     : https://prove2.me/submissions/86f6a4f8-2130-4011-a001-7cdc498f16e6

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_mul_linForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_one_left
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
variable {K : Type u} [Field K] {ι : Type} [Fintype ι]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {α : Type} [DecidableEq α] (L : α → ι → K) (ℓ : MvPowerSeries ι K)
    (cst : α → K) (h0 : MvPowerSeries.constantCoeff ℓ = 0)
    (hd : ∀ a, dirD (L a) ℓ = MvPowerSeries.C (cst a)) (s : Finset α) :
    ∀ G : MvPowerSeries ι K, jetPair (∏ i ∈ s, linForm (L i)) (ℓ * G) =
      ∑ b ∈ s, cst b * jetPair (∏ i ∈ s.erase b, linForm (L i)) G := by
  induction s using Finset.induction_on with
  | empty =>
    intro G
    simp [jetPair_one_left, h0]
  | insert a s ha ih =>
    intro G
    rw [Finset.prod_insert ha, mul_comm, jetPair_mul_linForm, Derivation.leibniz, hd, smul_eq_mul,
      smul_eq_mul, jetPair_add_right, ih, mul_comm G, jetPair_C_mul_right, Finset.sum_insert ha,
      Finset.erase_insert ha, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    have hab : a ≠ b := fun h => ha (h ▸ hb)
    rw [Finset.erase_insert_of_ne hab, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
      mul_comm (linForm (L a)), jetPair_mul_linForm]
end Formalism.DworkPowerSeriesWeights
