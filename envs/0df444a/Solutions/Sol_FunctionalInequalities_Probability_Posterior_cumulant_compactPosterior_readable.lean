-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.cumulant_compactPosterior_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:30:02.62065+00:00
-- url     : https://prove2.me/submissions/c42c5ddf-e485-4fd9-881a-3b89bde8cca6

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_logPartition_joint_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_logLaplace_compactPosterior_readable

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- **Posterior cumulants are `c`-derivatives of `ψ`**: `κ_m(μ_{c,Q}) = D_c^m ψ(c, Q)` for `m ≥ 1`. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) {m : ℕ} (hm : 1 ≤ m) :
    FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q : Measure E) m =
      iteratedFDeriv ℝ m (fun y => FunctionalInequalities.Probability.Posterior.logPartition μ y Q) c := by
  have hjoint := FunctionalInequalities.Probability.Posterior.contDiff_logPartition_joint_readable μ hc
  have hψ : ContDiff ℝ ∞ (fun y : E => FunctionalInequalities.Probability.Posterior.logPartition μ y Q) := by
    have hmap : ContDiff ℝ ∞ (fun y : E => (y, Q)) :=
      contDiff_id.prodMk contDiff_const
    have h := hjoint.comp hmap
    convert h using 1
    rfl
  have htrans : ContDiff ℝ ∞
      (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q) := by
    have hmap : ContDiff ℝ ∞ (fun z : E => c + z) :=
      contDiff_const.add contDiff_id
    have h := hψ.comp hmap
    convert h using 1
    rfl
  have hsub :
      iteratedFDeriv ℝ m
          (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q - FunctionalInequalities.Probability.Posterior.logPartition μ c Q) =
        iteratedFDeriv ℝ m (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q) -
          iteratedFDeriv ℝ m (fun _ : E => FunctionalInequalities.Probability.Posterior.logPartition μ c Q) := by
    have hfun :
        (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q - FunctionalInequalities.Probability.Posterior.logPartition μ c Q) =
          (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q) -
            (fun _ : E => FunctionalInequalities.Probability.Posterior.logPartition μ c Q) := by
      funext z
      rfl
    rw [hfun]
    exact iteratedFDeriv_sub
      (htrans.of_le (WithTop.coe_le_coe.mpr le_top))
      ((contDiff_const : ContDiff ℝ ∞
        (fun _ : E => FunctionalInequalities.Probability.Posterior.logPartition μ c Q)).of_le
        (WithTop.coe_le_coe.mpr le_top))
  have hm0 : m ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hconst :
      iteratedFDeriv ℝ m (fun _ : E => FunctionalInequalities.Probability.Posterior.logPartition μ c Q) = 0 :=
    iteratedFDeriv_const_of_ne hm0 _
  have hLL :
      FunctionalInequalities.Analysis.BakryEmery.logLaplace
          (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q : Measure E) =
        (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q - FunctionalInequalities.Probability.Posterior.logPartition μ c Q) := by
    funext z
    exact FunctionalInequalities.Probability.Posterior.logLaplace_compactPosterior_readable μ hc c Q z
  unfold FunctionalInequalities.Analysis.BakryEmery.cumulant
  rw [hLL]
  calc
    iteratedFDeriv ℝ m
        (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q - FunctionalInequalities.Probability.Posterior.logPartition μ c Q) 0 =
        (iteratedFDeriv ℝ m (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q) -
          iteratedFDeriv ℝ m (fun _ : E => FunctionalInequalities.Probability.Posterior.logPartition μ c Q)) 0 :=
      congrFun hsub 0
    _ = iteratedFDeriv ℝ m (fun z : E => FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q) 0 := by
      rw [hconst]
      simp
    _ = iteratedFDeriv ℝ m (fun y : E => FunctionalInequalities.Probability.Posterior.logPartition μ y Q) (c + 0) := by
      simpa only using
        (iteratedFDeriv_comp_add_left (𝕜 := ℝ) m c 0
          (f := fun y : E => FunctionalInequalities.Probability.Posterior.logPartition μ y Q))
    _ = iteratedFDeriv ℝ m (fun y : E => FunctionalInequalities.Probability.Posterior.logPartition μ y Q) c := by
      simp
