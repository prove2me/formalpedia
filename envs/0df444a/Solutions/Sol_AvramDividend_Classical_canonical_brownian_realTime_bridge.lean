-- Prove2me | solution 1 for AvramDividend.Classical.canonical_brownian_realTime_bridge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:47:52.073523+00:00
-- url     : https://prove2.me/submissions/e7887965-eb64-41e5-8467-849a0adda636

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Existence
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Theorems.Thm_ProbabilityTheory_IsPreBrownianReal_memHolder_mk_avram
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory NNReal Filter
open scoped NNReal

theorem solution :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion gaussianLimit,
      ∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        W.W (t : ℝ) ω = brownian t ω - brownian 0 ω := by
  have h := ProbabilityTheory.isPreBrownianReal_preBrownian
  have hmeas : ∀ t, Measurable (brownian t) := fun t =>
    h.exists_continuous_modification.choose_spec.1 t
  have hcont : ∀ ω, Continuous (brownian · ω) := fun ω =>
    continuous_iff_continuousAt.2 (fun t => by
      obtain ⟨U, hU, C, hC⟩ := ProbabilityTheory.IsPreBrownianReal.memHolder_mk_avram preBrownian h ω t
        (4⁻¹) (by norm_num) (by rw [inv_lt_inv₀ (by norm_num) (by norm_num)]; norm_num)
      exact (hC.continuousOn (by norm_num)).continuousAt hU)
  refine ⟨LevyStochCalc.Brownian.BrownianMotion.ofIsPreBrownianReal
    isBrownianReal_brownian_avram.toIsPreBrownianReal hmeas hcont, fun t ω => ?_⟩
  simp [LevyStochCalc.Brownian.BrownianMotion.ofIsPreBrownianReal, LevyStochCalc.Brownian.realTime]
