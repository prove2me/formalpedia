-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.norm_jetPair_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:59.140357+00:00
-- url     : https://prove2.me/submissions/742b5bd4-1398-41c1-b624-25bc8b426371

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
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type}
    (P : MvPolynomial ι K) (hP : P ∈ opInt K ι) (F : MvPowerSeries ι K) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ κ ∈ P.support, ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F‖ ≤ B) :
    ‖jetPair P F‖ ≤ B := by
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB fun κ hκ => ?_
  rw [mul_assoc, norm_mul]
  calc ‖coeff κ P‖ * ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F‖ ≤ 1 * B :=
        mul_le_mul (hP κ) (h κ hκ) (norm_nonneg _) zero_le_one
    _ = B := one_mul B
end Formalism.DworkPowerSeriesWeights
