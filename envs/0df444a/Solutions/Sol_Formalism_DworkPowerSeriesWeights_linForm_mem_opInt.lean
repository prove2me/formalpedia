-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.linForm_mem_opInt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:35.481543+00:00
-- url     : https://prove2.me/submissions/575501ff-1dad-4447-96b9-a522708eb6d7

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementQ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets

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
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type} [Fintype ι]
    (L : ι → K) (hL : ∀ x, ‖L x‖ ≤ 1) : linForm L ∈ opInt K ι := by
  classical
  unfold linForm
  refine Subring.sum_mem _ fun x _ => ?_
  intro κ
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, norm_mul]
  refine mul_le_one₀ (hL x) (norm_nonneg _) ?_
  split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights
