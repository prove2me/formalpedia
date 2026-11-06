-- Prove2me | solution 1 for BianchiIX.exists_normalized_core_regular_interval
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:36:41.981358+00:00
-- url     : https://prove2.me/submissions/0e518ec7-583c-469b-b970-eee1d8a75947

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_exists_Ioo_covering_Icc
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_Ioo_covering_of_eventually {s t : ℝ} {P : ℝ → Prop} (hst : s ≤ t)
    (hP : ∀ u ∈ Icc s t, ∀ᶠ v in 𝓝 u, P v) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ ∀ u ∈ Ioo l r, P u := by
  obtain ⟨l, r, hls, htr, hsub⟩ := exists_Ioo_covering_Icc hst isOpen_interior
    (fun u hu => mem_interior_iff_mem_nhds.mpr (hP u hu))
  exact ⟨l, r, hls, htr, fun u hu => interior_subset (hsub hu)⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

/-- Pointwise regularity on a closed prefix supplies the open interval needed by the inverse clock. -/
theorem solution {x : NormalizedState} {t₀ s t : ℝ}
    (hst : s ≤ t) (hdom : Icc s t ⊆ normalizedMaxDomain x t₀)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0)
    (hv : ∀ u ∈ Icc s t, 0 < toProjectiveState (normalizedMaxCurve x t₀ u) 2)
    (hd : ∀ u ∈ Icc s t, let y := toProjectiveState (normalizedMaxCurve x t₀ u)
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3)) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ ∀ u ∈ Ioo l r,
      u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0 ∧
      0 < toProjectiveState (normalizedMaxCurve x t₀ u) 2 ∧
      let y := toProjectiveState (normalizedMaxCurve x t₀ u)
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) := by
  apply exists_Ioo_covering_of_eventually hst
  intro u hu
  let β := fun v => toProjectiveState (normalizedMaxCurve x t₀ v)
  have hα := (hasDerivAt_normalizedMaxCurve (hdom hu)).continuousAt
  have hAc : ContinuousAt (fun v => 1 + normalizedMaxCurve x t₀ v 0) u :=
    continuousAt_const.add ((continuous_apply 0).continuousAt.comp hα)
  have hβ : ContinuousAt β u :=
    (contDiffAt_toProjectiveState 1 (ne_of_gt (hA u hu))).continuousAt.comp hα
  have hcoord (i : Fin 4) : ContinuousAt (fun v => β v i) u :=
    (continuous_apply i).continuousAt.comp hβ
  have hR : ContinuousAt (fun v => coreRadius (β v 0) (β v 2)) u := by
    unfold coreRadius coreEnergy
    exact (((hcoord 0).sub continuousAt_const).pow 2 |>.add ((hcoord 2).pow 2)).sqrt
  have hdc : ContinuousAt (fun v => coreClockFactor (coreRadius (β v 0) (β v 2)) (β v 1) (β v 3)) u :=
    continuousAt_const.sub (((hcoord 1).sub (hcoord 3)).pow 2 |>.div (hR.pow 2)
      (pow_ne_zero 2 (ne_of_gt (coreRadius_pos (hv u hu)))))
  have hmem : ∀ᶠ v in 𝓝 u, v ∈ normalizedMaxDomain x t₀ :=
    (isOpen_normalizedMaxDomain x t₀).mem_nhds (hdom hu)
  exact hmem.and
    ((hAc.eventually (isOpen_Ioi.mem_nhds (hA u hu))).and
      (((hcoord 2).eventually (isOpen_Ioi.mem_nhds (hv u hu))).and
        (hdc.eventually (isOpen_Ioi.mem_nhds (hd u hu)))))
