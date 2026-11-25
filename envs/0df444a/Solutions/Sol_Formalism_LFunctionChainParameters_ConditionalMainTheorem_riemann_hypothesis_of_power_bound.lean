-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ConditionalMainTheorem.riemann_hypothesis_of_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:59.369283+00:00
-- url     : https://prove2.me/submissions/f817bd44-0aa2-4fcf-ae2d-a6cb26910a08

import Definitions.Def_Formalism_SizeWindowBrackets_PowerBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_ZetaNonvanishing_RHofHalfPlane
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Theorems.Thm_Formalism_riemannHypothesis_of_zero_free_halfPlane
import Theorems.Thm_Formalism_zetaLandauEps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ConditionalMainTheorem
open Formalism
namespace Formalism.LFunctionChainParameters.ConditionalMainTheorem
theorem _root_.solution : PowerBoundGivesRiemannHypothesis := by
  intro C ε₁ hε₁ hG
  apply Formalism.riemannHypothesis_of_zero_free_halfPlane
  intro s hs
  refine Formalism.zetaLandauEps 1 (Or.inl rfl) (1 / 2) (by norm_num) (by norm_num) ?_ s hs
  intro ε' hε'
  set ε : ℝ := min (ε₁ / 2) (ε' / (|C| + 1)) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (div_pos hε' (by positivity))
  have hεlt : ε < ε₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨x₀, hx⟩ := hG ε hε0 hεlt
  refine ⟨1, max x₀ 1, fun x hx' => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx'
  have hCe : C * ε ≤ ε' := by
    have h1 : C * ε ≤ |C| * ε := mul_le_mul_of_nonneg_right (le_abs_self C) hε0.le
    have h2 : ε ≤ ε' / (|C| + 1) := min_le_right _ _
    have h3 : |C| * ε ≤ (|C| + 1) * ε := by nlinarith [abs_nonneg C]
    have h4 : (|C| + 1) * ε ≤ ε' := by
      rw [le_div_iff₀ (by positivity)] at h2; linarith
    linarith
  have := hx x (le_trans (le_max_left _ _) hx')
  calc (1 : ℝ) * Gz x = Gz x := one_mul _
    _ ≤ x ^ (1 / 2 + C * ε) := this
    _ ≤ x ^ (1 / 2 + ε') := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    _ = 1 * x ^ (1 / 2 + ε') := (one_mul _).symm
end Formalism.LFunctionChainParameters.ConditionalMainTheorem
