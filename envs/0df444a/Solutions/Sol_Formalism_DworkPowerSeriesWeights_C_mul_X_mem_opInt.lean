-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.C_mul_X_mem_opInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:15.665259+00:00
-- url     : https://prove2.me/submissions/72dce566-10a1-492f-ad5f-77e32a15fb43

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne

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
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : K)
    (hc : ‖c‖ ≤ 1) (j : σ) : C c * X j ∈ opInt K σ := by
  classical
  intro κ
  rw [coeff_C_mul, coeff_X, norm_mul]
  refine mul_le_one₀ hc (norm_nonneg _) ?_
  split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights
