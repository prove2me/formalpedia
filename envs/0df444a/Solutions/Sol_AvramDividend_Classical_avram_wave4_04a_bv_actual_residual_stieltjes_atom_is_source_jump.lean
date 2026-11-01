-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:16:18.531754+00:00
-- url     : https://prove2.me/submissions/668e1932-e16e-40dd-a1b2-dc59001c8dbe

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0,
      (∀ t : ℝ≥0, (F t : ℝ) = (t : ℝ) * X.drift - X.X t ω) ∧
      (∀ t : ℝ≥0, 0 < t →
        F.measure {t} =
          ENNReal.ofReal (Function.leftLim
            (fun u : ℝ≥0 => X.X u ω) t - X.X t ω)) := by
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV] with ω hmono
  let Y : ℝ≥0 → ℝ := fun t => (t : ℝ) * X.drift - X.X t ω
  have hm : Monotone Y := hmono
  have hright : ∀ t : ℝ≥0, Function.rightLim Y t = Y t := by
    intro t
    apply ContinuousWithinAt.rightLim_eq
    have hc : Continuous (fun u : ℝ≥0 => (u : ℝ) * X.drift) :=
      NNReal.continuous_coe.mul continuous_const
    exact hc.continuousWithinAt.sub (X.rightCont ω t)
  let F : StieltjesFunction ℝ≥0 := hm.stieltjesFunction
  have hF : ∀ t : ℝ≥0, (F t : ℝ) = Y t := by
    intro t
    change (hm.stieltjesFunction : ℝ≥0 → ℝ) t = Y t
    rw [hm.stieltjesFunction_eq]
    exact hright t
  have hFun : (fun t : ℝ≥0 => (F t : ℝ)) = Y := funext hF
  refine ⟨F, ?_, ?_⟩
  · intro t
    exact hF t
  · intro t ht
    letI : (𝓝[<] t).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    obtain ⟨l, hl⟩ := X.leftLim ω t ht
    have hlin :
        Tendsto (fun u : ℝ≥0 => (u : ℝ) * X.drift)
          (𝓝[<] t) (𝓝 ((t : ℝ) * X.drift)) :=
      (NNReal.continuous_coe.mul continuous_const).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have hleftY : Function.leftLim Y t = (t : ℝ) * X.drift - l :=
      leftLim_eq_of_tendsto (hlin.sub hl)
    have hleftX : Function.leftLim (fun u : ℝ≥0 => X.X u ω) t = l :=
      leftLim_eq_of_tendsto hl
    rw [StieltjesFunction.measure_singleton]
    change ENNReal.ofReal ((F t : ℝ) -
      Function.leftLim (fun u : ℝ≥0 => (F u : ℝ)) t) =
      ENNReal.ofReal (Function.leftLim
        (fun u : ℝ≥0 => X.X u ω) t - X.X t ω)
    rw [hF t, hFun, hleftY, hleftX]
    dsimp [Y]
    congr 1
    ring
