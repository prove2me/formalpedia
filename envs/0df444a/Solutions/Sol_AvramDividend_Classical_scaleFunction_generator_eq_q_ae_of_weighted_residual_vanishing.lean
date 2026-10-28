-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:09:31.353671+00:00
-- url     : https://prove2.me/submissions/71d65263-fb9e-4c16-940a-9dbbe7b0c571

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace S107ZP

/-- The zero process is a spectrally negative Lévy process (triplet `(0,0,0)`) on any probability
space and any filtration. -/
noncomputable def zeroLevy {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕 where
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
    haveI : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    exact (tendsto_nhds_unique h tendsto_const_nhds).symm.le
  adapted := fun _ => measurable_const
  indepIncrements := by
    intro s t _
    have : MeasurableSpace.comap (fun _ : Ω => (0 : ℝ) - 0) (inferInstance : MeasurableSpace ℝ) = ⊥ :=
      MeasurableSpace.comap_const _
    rw [this]
    exact ProbabilityTheory.indep_bot_left _
  stationaryIncrements := by
    intro s t _
    simp only [sub_self]
    exact ProbabilityTheory.IdentDistrib.refl aemeasurable_const
  laplace := by
    intro t θ _
    refine ⟨integrable_const _, ?_⟩
    simp [AvramDividend.Classical.laplaceExponent]

lemma X_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (t : ℝ≥0) (ω : Ω) : (zeroLevy P 𝓕).X t ω = 0 := rfl

lemma psi_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (θ : ℝ) : (zeroLevy P 𝓕).ψ θ = 0 := by
  simp [AvramDividend.Classical.SpectrallyNegativeLevy.ψ, AvramDividend.Classical.laplaceExponent,
    zeroLevy]

/-- For the zero process and `q > 0` the Laplace condition is vacuous. -/
lemma isScale {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (q : ℝ) (hq : 0 < q) :
    AvramDividend.Classical.IsScaleFunction (zeroLevy P 𝓕) q (fun y => max y 0) := by
  refine ⟨fun y hy => max_eq_right hy.le, fun y _ => le_max_right _ _,
    (continuous_id.max continuous_const).continuousOn,
    fun a _ b _ hab => max_le_max hab le_rfl, fun θ _ hθ => ?_⟩
  rw [psi_eq] at hθ; exact absurd hθ (not_lt.2 hq.le)

lemma generator_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (f : ℝ → ℝ) (x : ℝ) : (zeroLevy P 𝓕).generator f x = 0 := by
  simp [AvramDividend.Classical.SpectrallyNegativeLevy.generator, zeroLevy]

end S107ZP
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioo 0 a))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0),
    ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0) := by
  intro H
  let P : Measure PUnit.{1} := Measure.dirac PUnit.unit
  let 𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace PUnit.{1}) :=
    { seq := fun _ => ⊥, mono' := fun _ _ _ => le_rfl, le' := fun _ => bot_le }
  haveI : IsProbabilityMeasure P := by infer_instance

  have hc : ContinuousOn (fun x : ℝ => (S107ZP.zeroLevy P 𝓕).generator (fun y => max y 0) x -
      1 * (fun y : ℝ => max y 0) x) (Ioo 0 1) := by
    simp only [S107ZP.generator_eq]
    exact (continuous_const.sub (continuous_const.mul (continuous_id.max continuous_const))).continuousOn
  have h := H (S107ZP.zeroLevy P 𝓕) 1 (fun y => max y 0) (S107ZP.isScale P 𝓕 1 one_pos) 1 one_pos
    (by first | exact hc | exact hc.mono Ioo_subset_Ioi_self)
    (fun θ _ hθ => absurd hθ (by rw [S107ZP.psi_eq]; norm_num))
  simp only [S107ZP.generator_eq] at h
  rw [ae_restrict_iff' measurableSet_Ioo] at h
  have h0 : volume (Ioo (0 : ℝ) 1) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 h)
    simp only [Set.mem_ofPred_eq, _root_.not_imp]
    refine ⟨hx, ?_⟩
    rw [max_eq_left hx.1.le]; linarith [hx.1]
  rw [Real.volume_Ioo] at h0
  norm_num at h0
