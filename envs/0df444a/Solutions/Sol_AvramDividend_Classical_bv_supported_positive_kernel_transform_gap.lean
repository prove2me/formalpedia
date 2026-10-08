-- Prove2me | solution 1 for AvramDividend.Classical.bv_supported_positive_kernel_transform_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:42:54.599275+00:00
-- url     : https://prove2.me/submissions/48c15006-9127-493d-9b06-7f18a45a00e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_jump_magnitude_sfinite
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_tilted_kernel_measure
import Theorems.Thm_AvramDividend_Classical_bv_tilted_kernel_contractive_parameter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) :
    ∃ κ : Measure ℝ,
      SFinite κ ∧ κ (Iio (0 : ℝ)) = 0 ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) =
          ∫⁻ z : ℝ≥0, ENNReal.ofReal
            ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s)
            ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) ∧
      (∃ s : ℝ, 0 < s ∧
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) <
          ENNReal.ofReal X.drift) := by
  let μ : Measure ℝ≥0 :=
    X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  letI : SFinite μ := bv_jump_magnitude_sfinite X hX hbv
  have hδ : 0 < X.drift := (bv_standing_drift_pos X hX hbv).1
  let a : ℝ := q / X.drift
  have ha : 0 ≤ a := (div_pos hq hδ).le
  let τ : Measure ℝ :=
    (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)})
  let ω : Measure ℝ :=
    Measure.map (fun z : ℝ≥0 => (z : ℝ))
      (μ.withDensity (fun z : ℝ≥0 =>
        ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ)))))
  let γ : Measure ℝ :=
    (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun x : ℝ => ω (Iic x))
  let κ : Measure ℝ := τ + γ
  have hκsf : SFinite κ := by
    dsimp [κ, τ, γ]
    infer_instance
  have hbase :
      (volume.restrict (Ioi (0 : ℝ))) (Iio (0 : ℝ)) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iio]
    have hdisj : Disjoint (Iio (0 : ℝ)) (Ioi (0 : ℝ)) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact (lt_irrefl x) (lt_trans hx hy)
    rw [Set.disjoint_iff_inter_eq_empty.mp hdisj]
    simp
  have hτ : τ (Iio (0 : ℝ)) = 0 :=
    (withDensity_absolutelyContinuous _ _) hbase
  have hγ : γ (Iio (0 : ℝ)) = 0 :=
    (withDensity_absolutelyContinuous _ _) hbase
  have hκsupport : κ (Iio (0 : ℝ)) = 0 := by
    change (τ + γ) (Iio (0 : ℝ)) = 0
    rw [Measure.add_apply, hτ, hγ]
    simp
  have hkernel (s : ℝ) (hs : 0 < s) :
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) =
        ∫⁻ z : ℝ≥0,
          ENNReal.ofReal
            ((1 - Real.exp (-(s + a) * (z : ℝ))) / s) ∂μ := by
    exact positiveLaplace_tilted_kernel_measure μ a s ha hs
  refine ⟨κ, hκsf, hκsupport, ?_, ?_⟩
  · intro s hs
    exact hkernel s hs
  · obtain ⟨n, hn⟩ :=
      bv_tilted_kernel_contractive_parameter X hX hbv q hq
    dsimp at hn
    refine ⟨((n : ℝ) + 1) - a, hn.1, ?_⟩
    rw [hkernel _ hn.1]
    exact hn.2
