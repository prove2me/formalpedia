-- Prove2me | solution 1 for FunctionalInequalities.KLS.RegularPotential.covariance_pos_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:19.533301+00:00
-- url     : https://prove2.me/submissions/f4d3b119-bb33-4572-bd89-e2186f091c46

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Isotropic
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_memLp_id_two_readable

section
noncomputable section
open MeasureTheory Set
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
/-- A law `ν = volume.tilted (-W)` with continuous convex `W` is log-concave: its density
`e^{-W} / ∫ e^{-W}` is a log-concave Borell density (`IsBorellDensity.compactLogConcave`). -/
theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) : LogConcave ν := by
  exact
    IsBorellDensity.compactLogConcave
      (isBorellDensity_of_eq_tilted_readable hνW hW hconv)
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section
variable {V : E → ℝ} {a b : ℝ}
theorem FunctionalInequalities.KLS.RegularPotential.logConcave_law (hV : RegularPotential V a b) : LogConcave hV.law := by
  have hW : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  exact LogConcave.logConcave_of_eq_tilted (ν := hV.law) rfl hW.continuous
    (Analysis.BakryEmery.convexOn_of_hessian_ge_readable hW hV.pos.le hV.lower)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
end
end
end
end

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {V : E → ℝ} {a b : ℝ}
/-- A regular law has a finite second moment. -/
theorem FunctionalInequalities.KLS.RegularPotential.memLp_id_two (hV : KLS.RegularPotential V a b) : MemLp id 2 (hV.law : Measure E) :=
  hV.logConcave_law.memLp_id_two_readable
/-- Lebesgue measure is absolutely continuous with respect to a regular law (positive density). -/
theorem FunctionalInequalities.KLS.RegularPotential.volume_absolutelyContinuous_law (hV : KLS.RegularPotential V a b) :
    (volume : Measure E) ≪ (hV.law : Measure E) :=
  absolutelyContinuous_tilted hV.integrable_exp_neg
/-- The covariance of a regular law is positive definite. -/
theorem solution (hV : FunctionalInequalities.KLS.RegularPotential V a b) {v : E} (hv : v ≠ 0) :
    0 < inner ℝ (FunctionalInequalities.Covariance.operator (hV.law : Measure E) v) v := by
  rw [FunctionalInequalities.Covariance.operator_inner, covarianceBilin_self (FunctionalInequalities.KLS.RegularPotential.memLp_id_two hV)]
  rcases (variance_nonneg (fun x => inner ℝ v x) (hV.law : Measure E)).lt_or_eq with h | h
  · exact h
  exfalso
  have hX : MemLp (fun x => inner ℝ v x) 2 (hV.law : Measure E) := by
    simpa only [Function.comp_def, id_eq, innerSL_apply_apply] using
      (innerSL ℝ v).comp_memLp' (FunctionalInequalities.KLS.RegularPotential.memLp_id_two hV)
  have hae := ae_eq_integral_of_variance_eq_zero hX h.symm
  have hvol := (FunctionalInequalities.KLS.RegularPotential.volume_absolutelyContinuous_law hV).ae_le hae
  have heq : (fun x : E => inner ℝ v x) =
      fun _ => ∫ x, inner ℝ v x ∂(hV.law : Measure E) :=
    Measure.eq_of_ae_eq hvol (by fun_prop) continuous_const
  have h0 := congrFun heq 0
  have hvv := congrFun heq v
  simp only [inner_zero_right] at h0
  rw [← h0, real_inner_self_eq_norm_sq] at hvv
  exact hv (norm_eq_zero.mp (sq_eq_zero_iff.mp hvv))
