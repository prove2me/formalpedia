-- Prove2me | solution 1 for Formalism.ValuationGridEstimates.tower_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:40:59.887266+00:00
-- url     : https://prove2.me/submissions/5ef79851-7750-46c0-a032-5372095e3b59

import Definitions.Def_Formalism_TowerValuationBounds_HermitianSumValuationBound
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ValuationGridEstimates
open Finset
namespace Formalism.ValuationGridEstimates
theorem _root_.solution : TowerProductRatioFormula := by
  intro K _ L L0 c u c0 u0 p q e Ω Ω' hΩ hΩ' hL h1 h2 h3 h4
  rw [tower_bound K L c u p q e (fun k a b => (hL k a b).1) h1 h2,
    tower_bound K L0 c0 u0 p q e (fun k a b => (hL k a b).2) h3 h4]
  have hq : Ω' / Ω ≠ 0 := div_ne_zero hΩ' hΩ
  have e1 : (c p q * Ω' / Ω) / (c0 p q * Ω' / Ω) = c p q / c0 p q := by
    rw [mul_div_assoc (c p q) Ω' Ω, mul_div_assoc (c0 p q) Ω' Ω, mul_div_mul_right _ _ hq]
  rw [e1]
  simp only [Finset.prod_div_distrib]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring
end Formalism.ValuationGridEstimates
