-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.neglog_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:32.579654+00:00
-- url     : https://prove2.me/submissions/8358ce4d-4887-461b-a24f-f9a9dad1607b

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_norm_nat
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_neglog_zpow
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Polynomial Finset
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :
    -Real.logb p ‖(n : ℚ_[p])‖ = padicValNat p n := by
  rw [norm_nat p n hn, neglog_zpow]
  simp
end Formalism.GM.MeanGammaLemmas
