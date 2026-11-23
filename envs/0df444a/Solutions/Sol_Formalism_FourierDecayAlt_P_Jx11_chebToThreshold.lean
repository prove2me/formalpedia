-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx11.chebToThreshold
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:28.498742+00:00
-- url     : https://prove2.me/submissions/0307fcc9-382d-40ee-8a61-616cf5914f29

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdBelowOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx11
namespace Formalism.FourierDecayAlt.P.Jx11
theorem _root_.solution : ChebToThreshold := by
  intro L f d pl sa al bt κ len lv be X B Mx hκ hlen hbt hsa h1 h2
  have hz : κ ^ (1 - (d : ℤ)) = κ * (κ ^ d)⁻¹ := by
    rw [zpow_sub₀ hκ.ne', zpow_one, zpow_natCast, div_eq_mul_inv]
  have hfac : ∀ a, (1 / 2) * (4 / (bt a - al a)) ^ d * (κ * be (pl a)) =
      κ ^ (1 - (d : ℤ)) * ((1 / 2) * be (pl a) * (4 * κ / len) ^ d) := by
    intro a
    rw [hbt a, hz, div_pow, div_pow, mul_pow]
    field_simp
  have hc0 : 0 ≤ ∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d := by
    apply Finset.prod_nonneg
    intro a _
    rw [hbt a]; positivity
  have hP : 0 < ∏ _a : Fin L, κ ^ (1 - (d : ℤ)) := Finset.prod_pos (fun _ _ => zpow_pos hκ _)
  have h3 : (∏ a, sa a) * X ≤ (∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d) * ((∏ a, κ * be (pl a)) * Mx) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hc0)
  have h4 : (∏ a, sa a) = (∏ _a : Fin L, κ ^ (1 - (d : ℤ))) * ∏ a, lv (pl a) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun a _ => hsa a)
  have h5 : (∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d) * (∏ a, κ * be (pl a)) =
      (∏ _a : Fin L, κ ^ (1 - (d : ℤ))) * ∏ a, (1 / 2) * be (pl a) * (4 * κ / len) ^ d := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun a _ => hfac a)
  rw [h4, ← mul_assoc, h5, mul_assoc, mul_assoc] at h3
  exact le_of_mul_le_mul_left h3 hP
end Formalism.FourierDecayAlt.P.Jx11
