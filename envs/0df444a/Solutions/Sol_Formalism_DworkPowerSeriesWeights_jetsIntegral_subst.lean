-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetsIntegral_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:15:45.607898+00:00
-- url     : https://prove2.me/submissions/2365321d-54bb-4fbe-a6d2-733cffe754ec

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_monomial_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_jetPair_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_C_mul_X_mem_opInt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_pair_linearity


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
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (A : ι → ι' → K) (hA : ∀ i j, ‖A i j‖ ≤ 1) (sg : MvPowerSeries ι' K)
    (hsg : JetsIntegral sg) :
    JetsIntegral (MvPowerSeries.subst
      (fun j : ι' => (∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i : MvPowerSeries ι K))
      sg) := by
  intro κ
  rw [← jetPair_monomial_left, jet_pair_linearity K ι ι' A]
  refine norm_jetPair_le _ ?_ _ 1 zero_le_one fun μ _ => hsg μ
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod]
  refine Subring.prod_mem _ fun i _ => Subring.pow_mem _ ?_ _
  exact Subring.sum_mem _ fun j _ => C_mul_X_mem_opInt _ (hA i j) j
end Formalism.DworkPowerSeriesWeights
