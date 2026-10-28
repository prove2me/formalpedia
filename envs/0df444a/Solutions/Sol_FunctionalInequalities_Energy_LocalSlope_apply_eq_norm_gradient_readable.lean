-- Prove2me | solution 1 for FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:55.180318+00:00
-- url     : https://prove2.me/submissions/d43462a8-8c28-4662-9aae-dda5023a441a

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_LocalSlope_Gradient

noncomputable section
open MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- Step 1: the one-moving-point local slope equals the derivative norm at a differentiable
point, expressed through the canonical Hilbert gradient. No nontriviality premise is needed. -/
theorem solution
    (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f x) :
    FunctionalInequalities.Energy.LocalSlope.apply f x = ENNReal.ofReal ‖gradient f x‖ := by
  rw [FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.norm_gradient_eq_norm_fderiv]
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨r, hr, hrem⟩ := Metric.eventually_nhds_iff_ball.mp
      (hf.hasFDerivAt.isLittleO.bound hεr)
    calc
      FunctionalInequalities.Energy.LocalSlope.apply f x ≤ ENNReal.ofReal (‖fderiv ℝ f x‖ + ε) := by
        unfold FunctionalInequalities.Energy.LocalSlope.apply
        refine iInf_le_of_le r (iInf_le_of_le hr ?_)
        refine iSup_le fun y => iSup_le fun hy => ?_
        apply ENNReal.ofReal_le_ofReal
        by_cases hyx : y = x
        · subst y
          simp only [dist_self, div_zero]
          positivity
        · apply (div_le_iff₀ (dist_pos.mpr hyx)).2
          rw [dist_eq_norm, dist_eq_norm]
          calc
            ‖f y - f x‖ = ‖(f y - f x - (fderiv ℝ f x) (y - x)) +
                (fderiv ℝ f x) (y - x)‖ := by rw [sub_add_cancel]
            _ ≤ ‖f y - f x - (fderiv ℝ f x) (y - x)‖ +
                ‖(fderiv ℝ f x) (y - x)‖ := norm_add_le _ _
            _ ≤ ε * ‖y - x‖ + ‖fderiv ℝ f x‖ * ‖y - x‖ :=
              add_le_add (hrem y hy) ((fderiv ℝ f x).le_opNorm _)
            _ = (‖fderiv ℝ f x‖ + ε) * ‖y - x‖ := by ring
      _ = ENNReal.ofReal ‖fderiv ℝ f x‖ + ε := by
        have hadd (a : ℝ) (ha : 0 ≤ a) :
            ENNReal.ofReal (a + (ε : ℝ)) = ENNReal.ofReal a + (ε : ENNReal) := by
          convert! ENNReal.ofReal_add ha ε.2 using 1
          simp
        exact hadd _ (by positivity)
  · unfold FunctionalInequalities.Energy.LocalSlope.apply
    refine le_iInf fun r => le_iInf fun hr => ?_
    let S : ENNReal := ⨆ (y : E) (_ : dist y x < r),
      ENNReal.ofReal (dist (f y) (f x) / dist y x)
    change ENNReal.ofReal ‖fderiv ℝ f x‖ ≤ S
    by_cases hS : S = ⊤
    · simp [hS]
    apply (ENNReal.ofReal_le_iff_le_toReal hS).2
    apply hf.hasFDerivAt.le_of_lip' ENNReal.toReal_nonneg
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    by_cases hyx : y = x
    · subst y
      simp
    · have hq : ENNReal.ofReal (dist (f y) (f x) / dist y x) ≤ S :=
        le_iSup_of_le y (le_iSup_of_le hy le_rfl)
      have := (ENNReal.ofReal_le_iff_le_toReal hS).1 hq
      have := (div_le_iff₀ (dist_pos.mpr hyx)).1 this
      simpa only [dist_eq_norm] using this
