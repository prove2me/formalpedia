-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.WeakCauchyRiemannOn.congr_ae
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:39:43.913585+00:00
-- url     : https://prove2.me/submissions/46858044-817c-485c-a635-91081f8f91db

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.WeakCauchyRiemannOn.congr_ae
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_dbar_eq_zero_of_notMem_tsupport
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {f g : ℂ → ℂ} {U : Set ℂ}
    (hg : WeakCauchyRiemannOn g U) (hae : ∀ᵐ z : ℂ, z ∈ U → f z = g z) :
    WeakCauchyRiemannOn f U := by

  intro φ hφ hφc hφU
  have : ∫ z : ℂ, f z * dbar φ z = ∫ z : ℂ, g z * dbar φ z := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    by_cases hzU : z ∈ U
    · rw [hz hzU]
    · have : dbar φ z = 0 :=
        dbar_eq_zero_of_notMem_tsupport fun h => hzU (hφU h)
      rw [this, mul_zero, mul_zero]
  rw [this]
  exact hg φ hφ hφc hφU
