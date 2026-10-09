-- Prove2me | solution 1 for AvramDividend.Classical.bv_root_discounted_tail_kernel_package
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:23:46.673007+00:00
-- url     : https://prove2.me/submissions/dbe66e42-b342-404a-a58a-e66dcf7cd59d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_esscher_discounted_tail_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hδ : 0 < X.drift) :
    ∃ (κ : Measure ℝ),
      SFinite κ ∧ κ (Iio (0 : ℝ)) = 0 ∧
      κ Set.univ < ENNReal.ofReal X.drift ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
          (∫⁻ z : ℝ≥0,
            ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
              ENNReal.ofReal
                ((1 - Real.exp (-(s * (z : ℝ)))) / s)
              ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) := by
  let μ : Measure ℝ≥0 :=
    X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  let μφ : Measure ℝ≥0 :=
    μ.withDensity (fun z : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
  let κ : Measure ℝ :=
    (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun t : ℝ => μφ {z : ℝ≥0 | t < (z : ℝ)})
  have hsf : SFinite κ := by
    dsimp [κ]
    infer_instance
  have hbase :
      (volume.restrict (Ioi (0 : ℝ))) (Iio (0 : ℝ)) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iio]
    have hd : Disjoint (Iio (0 : ℝ)) (Ioi (0 : ℝ)) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact (lt_irrefl x) (lt_trans hx hy)
    rw [Set.disjoint_iff_inter_eq_empty.mp hd]
    simp
  have hsupp : κ (Iio (0 : ℝ)) = 0 :=
    (withDensity_absolutelyContinuous _ _) hbase
  obtain ⟨hA, hAδ⟩ :=
    bv_esscher_root_subcritical_kernel_mass X hbv q hq φ hφ hroot
  have hpos :
      0 ≤ᵐ[μ] (fun z : ℝ≥0 =>
        (z : ℝ) * Real.exp (-(φ * (z : ℝ)))) := by
    filter_upwards with z
    exact mul_nonneg (NNReal.coe_nonneg z) (Real.exp_pos _).le
  have hmass :=
    esscher_tail_kernel_mass_as_discounted_first_moment μ φ
  have htoReal :
      ENNReal.ofReal (∫ z : ℝ≥0,
        (z : ℝ) * Real.exp (-(φ * (z : ℝ))) ∂μ) =
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal
            ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂μ) :=
    ofReal_integral_eq_lintegral_ofReal hA hpos
  have hκmass : κ Set.univ < ENNReal.ofReal X.drift := by
    rw [show κ Set.univ =
      (∫⁻ z : ℝ≥0,
        ENNReal.ofReal
          ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂μ) from hmass]
    rw [← htoReal]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hAδ
  refine ⟨κ, hsf, hsupp, hκmass, ?_⟩
  intro s hs
  exact positiveLaplace_esscher_discounted_tail_kernel μ φ s hs
