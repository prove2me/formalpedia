-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.derived_energy_L2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:32:17.174983+00:00
-- url     : https://prove2.me/submissions/92e9018e-bfef-46a5-bdbe-5643c1f5d05e

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : WeightedIntegrable := by
  intro B T _ f v C p N hpN hmf hf0 hfb h1 h2
  have hg : Integrable (fun ω => |C| * ∑ t, (‖v t ω‖ ^ 2 + (B.G ω) ^ (2 * p) * ‖v t ω‖ ^ 2)) B.μ :=
    (integrable_finset_sum _ fun t _ => (h1 t).add (h2 t)).const_mul _
  refine hg.mono' hmf.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]
  refine (hfb ω).trans ?_
  have hG := B.G_pos ω
  have hexp : (0:ℝ) ≤ (2 * p : ℝ) - N := by
    have : (N:ℝ) ≤ 2 * p := by exact_mod_cast hpN
    linarith
  have hpow : (B.G ω) ^ ((2 * p : ℝ) - N) ≤ 1 + (B.G ω) ^ (2 * p) := by
    rcases le_total (B.G ω) 1 with h | h
    · have := Real.rpow_le_one hG.le h hexp
      have h' : 0 ≤ (B.G ω) ^ (2 * p) := by positivity
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h (show (2 * p : ℝ) - N ≤ ((2 * p : ℕ) : ℝ) by push_cast; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
      rw [Real.rpow_natCast] at this
      linarith
  have hS : 0 ≤ ∑ t, ‖v t ω‖ ^ 2 := Finset.sum_nonneg fun t _ => by positivity
  have hr : 0 ≤ (B.G ω) ^ ((2 * p : ℝ) - N) := Real.rpow_nonneg hG.le _
  calc C * (B.G ω) ^ ((2 * p : ℝ) - N) * ∑ t, ‖v t ω‖ ^ 2
      ≤ |C| * (B.G ω) ^ ((2 * p : ℝ) - N) * ∑ t, ‖v t ω‖ ^ 2 := by
        gcongr; exact le_abs_self C
    _ ≤ |C| * (1 + (B.G ω) ^ (2 * p)) * ∑ t, ‖v t ω‖ ^ 2 := by gcongr
    _ = _ := by
        rw [mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
end Formalism.FourierDecayAlt.P.LEx1
