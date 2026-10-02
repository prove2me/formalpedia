-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_continuous_of_ac_levy
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:09:30.759243+00:00
-- url     : https://prove2.me/submissions/b31b4da2-4c75-4400-97c0-67204cf3a53d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace Cex156517ba

open AvramDividend.Classical

/-- The zero process on the one-point space: triplet `(0, 0, 0)`. -/
noncomputable def zeroLevy :
    SpectrallyNegativeLevy (Ω := Unit) (Measure.dirac ())
      (⊥ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit)) where
  X := fun _ _ => 0
  c := 0
  σ := 0
  ν := 0
  isProbability := inferInstance
  σ_nonneg := le_rfl
  ν_Ici := by simp
  ν_integrable := by simp
  X_zero := fun _ => rfl
  rightCont := fun _ _ => continuousWithinAt_const
  leftLim := fun _ _ _ => ⟨0, tendsto_const_nhds⟩
  noPosJumps := by
    intro ω t l ht h
    have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    exact le_of_eq (tendsto_nhds_unique tendsto_const_nhds h)
  adapted := fun _ => measurable_const
  indepIncrements := by
    intro s t _
    show Indep (MeasurableSpace.comap (fun _ : Unit => (0 : ℝ) - 0) inferInstance) _ _
    rw [MeasurableSpace.comap_const]
    exact indep_bot_left _
  stationaryIncrements := by
    intro s t _
    show IdentDistrib (fun _ : Unit => (0 : ℝ) - 0) (fun _ : Unit => (0 : ℝ)) _ _
    simp only [sub_self]
    exact IdentDistrib.refl aemeasurable_const
  laplace := by
    intro t θ _
    refine ⟨integrable_const _, ?_⟩
    simp [laplaceExponent]

theorem zeroLevy_ψ (θ : ℝ) : zeroLevy.ψ θ = 0 := by
  simp [SpectrallyNegativeLevy.ψ, laplaceExponent, zeroLevy]

/-- A kinked candidate. -/
noncomputable def Wk (y : ℝ) : ℝ := max 0 (y - 1)

theorem Wk_scale : IsScaleFunction zeroLevy 1 Wk := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    simp only [Wk]
    exact max_eq_left (by linarith)
  · intro y _
    exact le_max_left _ _
  · exact (continuous_const.max (continuous_id.sub continuous_const)).continuousOn
  · intro a _ b _ hab
    exact max_le_max le_rfl (by linarith)
  · intro θ _ hθ
    rw [zeroLevy_ψ] at hθ
    exact absurd hθ (by norm_num)

theorem deriv_Wk_lt {y : ℝ} (hy : y < 1) : deriv Wk y = 0 := by
  have h : Wk =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hy] with z hz
    simp only [Wk]
    exact max_eq_left (by simp only [mem_Iio] at hz; linarith)
  rw [h.deriv_eq]
  simp

theorem deriv_Wk_gt {y : ℝ} (hy : 1 < y) : deriv Wk y = 1 := by
  have h : Wk =ᶠ[𝓝 y] fun z => z - 1 := by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    simp only [Wk]
    exact max_eq_right (by simp only [mem_Ioi] at hz; linarith)
  rw [h.deriv_eq]
  simp

theorem not_cont : ¬ ContinuousOn (deriv Wk) (Ioi 0) := by
  intro hc
  have hca : ContinuousAt (deriv Wk) 1 :=
    hc.continuousAt (Ioi_mem_nhds (by norm_num))
  have hL : Tendsto (deriv Wk) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (deriv_Wk_lt hz).symm
  have hR : Tendsto (deriv Wk) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (deriv_Wk_gt hz).symm
  have e0 : deriv Wk 1 = 0 :=
    tendsto_nhds_unique (hca.tendsto.mono_left nhdsWithin_le_nhds) hL
  have e1 : deriv Wk 1 = 1 :=
    tendsto_nhds_unique (hca.tendsto.mono_left nhdsWithin_le_nhds) hR
  rw [e0] at e1
  norm_num at e1

theorem cex : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hac : X.ν ≪ volume) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W),
    ContinuousOn (deriv W) (Ioi 0)) := by
  intro H
  have hac : zeroLevy.ν ≪ volume := by
    show (0 : Measure ℝ) ≪ volume
    exact Measure.AbsolutelyContinuous.zero _
  exact not_cont (H zeroLevy hac 1 one_pos Wk Wk_scale)

end Cex156517ba

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical in
theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hac : X.ν ≪ volume) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W),
    ContinuousOn (deriv W) (Ioi 0)) := by
  exact Cex156517ba.cex
