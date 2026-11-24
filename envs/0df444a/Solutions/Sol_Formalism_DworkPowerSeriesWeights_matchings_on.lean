-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.matchings_on
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:46.551804+00:00
-- url     : https://prove2.me/submissions/e4da0933-c437-4a1b-b4d1-de16c4a1d04a

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_mul_linForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_one_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_quadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_polar_comm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_mvExp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_insert
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_edgeW_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_invOn_empty
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_invOn_insert

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
theorem _root_.solution (c : ι → ι → K) (S : K) {n : ℕ} (L : Fin n → ι → K) (s : Finset (Fin n)) :
    ∀ h : MvPowerSeries ι K,
      jetPair (∏ i ∈ s, linForm (L i)) (mvExp ((-S) • quadSer c) * h) =
        ∑ σ ∈ invOn s, edgeW (fun i j => -S * polar c (L i) (L j)) σ *
          jetPair (∏ i ∈ s.filter (fun i => σ i = i), linForm (L i)) h := by
  induction s using Finset.strongInduction with
  | H s ih =>
    intro h
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · have h0 : MvPowerSeries.constantCoeff ((-S) • quadSer c) = 0 := by
        rw [MvPowerSeries.smul_eq_C_mul, map_mul, constantCoeff_quadSer, mul_zero]
      rw [invOn_empty, Finset.sum_singleton, edgeW_one, Finset.filter_empty, Finset.prod_empty,
        jetPair_one_left, jetPair_one_left, map_mul, constantCoeff_mvExp _ h0]
    · obtain ⟨t, hat, rfl⟩ : ∃ t, a ∉ t ∧ insert a t = s :=
        ⟨s.erase a, Finset.notMem_erase a s, Finset.insert_erase ha⟩
      rw [jet_insert c S L a t hat h,
        sum_invOn_insert (fun i j => -S * polar c (L i) (L j))
          (fun i j => by rw [polar_comm]) (fun F => jetPair (∏ i ∈ F, linForm (L i)) h) a t hat,
        ih t (Finset.ssubset_insert hat)]
      congr 1
      · refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.prod_insert (fun hh => hat (Finset.mem_of_mem_filter a hh)),
          mul_comm (linForm (L a)), jetPair_mul_linForm]
      · refine Finset.sum_congr rfl fun b hb => ?_
        rw [ih (t.erase b) ((Finset.erase_subset b t).trans_ssubset (Finset.ssubset_insert hat))]
end Formalism.DworkPowerSeriesWeights
