-- Prove2me | solution 1 for BianchiIX.exists_exitTail_uniform_tube_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:00:07.891199+00:00
-- url     : https://prove2.me/submissions/2909d35f-3cc9-4b9a-aea0-a3eda0ad482c

import Definitions.Def_BianchiIX_TerminalConnectionData
import Theorems.Thm_BianchiIX_exists_exitTail_strict_prefix_bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isClosed_exitTailRegion (α b A D : ℝ) : IsClosed {Y | exitTailRegion α b A D Y} := by
  have hsum : Continuous (fun Y : ExitTailState => |Y 1| + |Y 2|) := by fun_prop
  have hrad : Continuous (fun Y : ExitTailState => |Y 0 - (2 + 2 * α)|) := by fun_prop
  exact ((isClosed_le continuous_const (continuous_apply 0)).inter
    (isClosed_le (continuous_apply 0) continuous_const)).inter
    ((isClosed_le (continuous_apply 1).abs continuous_const).inter
      ((isClosed_le (continuous_apply 2).abs continuous_const).inter
        ((isClosed_le hsum continuous_const).inter (isClosed_le hrad continuous_const))))


/-- Every existing tail segment stays in the improved tube; no tube hypothesis is assumed. -/
theorem solution {K : ℝ} (hK : 0 ≤ K) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ∀ T α b : ℝ, ∀ Y : ℝ → ExitTailState,
      0 ≤ T → (0 ≤ α ∧ α ≤ 1) → 0 < b → b * (1 + T) ≤ ε → α * T ≤ K →
      Y 0 0 = 2 + 2 * α → |Y 0 1| + |Y 0 2| ≤ b →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      ∀ r ∈ Icc 0 T, exitTailRegion α b A (80 * A) (Y r) ∧
        (∀ i : Fin 2, Y r i.succ = Y 0 i.succ * exitTailMultiplier Y i r ∧
          2 / A ≤ exitTailMultiplier Y i r ∧ exitTailMultiplier Y i r ≤ A / 2) ∧
        |Y r 1| + |Y r 2| ≤ A * b / 2 ∧ |Y r 0 - Y 0 0| ≤ 40 * A * b := by
  obtain ⟨A, hA, ε₀, hε₀, _, HP⟩ := exists_exitTail_strict_prefix_bounds hK
  have hA0 : 0 < A := by linarith only [hA]
  let ε := min ε₀ (1 / (1000 * A))
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  refine ⟨A, hA, ε, hε, ?_⟩
  intro T α b Y hT hα hb hsmall hwait hR0 hw0 hY
  have hbε : b ≤ ε := by nlinarith only [hsmall, mul_nonneg hb.le hT]
  have hAbsmall : A * b ≤ 1 / 1000 := by
    have H := (le_div_iff₀ (by positivity : 0 < 1000 * A)).mp (hbε.trans (min_le_right _ _))
    nlinarith only [H]
  have hAb : 0 < A * b := mul_pos hA0 hb
  let S := {s : ℝ | exitTailRegion α b A (80 * A) (Y s)}
  have hs0 : (0 : ℝ) ∈ S := by
    have hsum : |Y 0 1| + |Y 0 2| ≤ A * b := by nlinarith only [hw0, hA, hb]
    refine ⟨?_, ?_, ?_, hsum, ?_⟩
    · rw [hR0]
      constructor <;> linarith only [hα.1, hα.2]
    · linarith only [hsum, hAbsmall, abs_nonneg (Y 0 2)]
    · linarith only [hsum, hAbsmall, abs_nonneg (Y 0 1)]
    · rw [hR0, sub_self, abs_zero]
      positivity
  have hprefix (r : ℝ) (hr : r ∈ Icc 0 T) (hreg : ∀ s ∈ Icc 0 r, s ∈ S) :=
    HP r α b Y hr.1 hα.1 hb.le
      ((mul_le_mul_of_nonneg_left (add_le_add le_rfl hr.2) hb.le).trans (hsmall.trans (min_le_left _ _)))
      ((mul_le_mul_of_nonneg_left hr.2 hα.1).trans hwait)
      (fun s hs => hY s ⟨hs.1, hs.2.trans hr.2⟩) hreg hw0
  have hclosed : IsClosed (S ∩ Icc 0 T) := by
    have H := (HasDerivAt.continuousOn hY).preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_exitTailRegion α b A (80 * A))
    change IsClosed (Icc 0 T ∩ S) at H
    rwa [inter_comm] at H
  have hwhole : Icc 0 T ⊆ S := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hs0
    intro r hr hbefore
    have H := hprefix r ⟨hr.1, hr.2.le⟩ hbefore
    have hrad : |Y r 0 - (2 + 2 * α)| ≤ 40 * A * b := by simpa only [hR0] using H.2.2
    have hlo : 7 / 4 < Y r 0 := by linarith only [(abs_le.mp hrad).1, hα.1, hAbsmall]
    have hhi : Y r 0 < 17 / 4 := by linarith only [(abs_le.mp hrad).2, hα.2, hAbsmall]
    have hu : |Y r 1| < 1 / 100 := by linarith only [H.2.1, hAbsmall, abs_nonneg (Y r 2)]
    have hw : |Y r 2| < 1 / 100 := by linarith only [H.2.1, hAbsmall, abs_nonneg (Y r 1)]
    have hs : |Y r 1| + |Y r 2| < A * b := by linarith only [H.2.1, hAb]
    have hd : |Y r 0 - (2 + 2 * α)| < 80 * A * b := by linarith only [hrad, hAb]
    have hc (i : Fin 3) := (hasDerivAt_pi.mp (hY r ⟨hr.1, hr.2.le⟩) i).continuousAt
    have hnear : ∀ᶠ s in 𝓝 r, s ∈ S := by
      filter_upwards [(hc 0).eventually (Ioo_mem_nhds hlo hhi),
        (hc 1).abs.eventually (isOpen_Iio.mem_nhds hu),
        (hc 2).abs.eventually (isOpen_Iio.mem_nhds hw),
        ((hc 1).abs.add (hc 2).abs).eventually (isOpen_Iio.mem_nhds hs),
        ((hc 0).sub continuousAt_const).abs.eventually (isOpen_Iio.mem_nhds hd)] with s hR hu hw hs hd
      exact ⟨⟨hR.1.le, hR.2.le⟩, hu.le, hw.le, hs.le, hd.le⟩
    exact hnear.filter_mono nhdsWithin_le_nhds
  intro r hr
  exact ⟨hwhole hr, hprefix r hr (fun s hs => hwhole ⟨hs.1, hs.2.trans hr.2⟩)⟩
