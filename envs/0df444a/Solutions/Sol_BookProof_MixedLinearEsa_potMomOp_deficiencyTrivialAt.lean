-- Prove2me | solution 1 for BookProof.MixedLinearEsa.potMomOp_deficiencyTrivialAt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T13:12:39.612402+00:00
-- url     : https://prove2.me/submissions/8df9ad5e-44c3-4a0c-9152-8fe44d6e7161
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.potMomOp_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Theorems.Thm_BookProof_MixedLinearEsa_momentumOp_eq_zero_of_compactSupport_test
import Theorems.Thm_BookProof_MixedLinearEsa_potMomOp_gauge
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_StrichartzWave_schwartzEquiv_coe
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.MixedLinearEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine
open BookProof.FourierMultiplierEsa
open BookProof.ShiftedHermiteCore
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! The platform's published `Def_ChapterMixedLinearEsa` carries `phaseFun` /
`phaseSchwartz` but not the two auxiliary lemmas below, and a solution may not
rely on unpublished declarations (`norm_phaseFun` then resolves to the
HermiteProductCore one of a different type).  They are restated locally as
`private`, so the file is standalone. -/

private theorem norm_phaseFun' (θ : V → ℝ) (x : V) : ‖phaseFun θ x‖ = 1 := by
  rw [BookProof.MixedLinearEsa.phaseFun, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem phaseSchwartz_apply' {θ : V → ℝ}
    (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (φ : 𝓢(V, ℂ)) (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) :
    phaseSchwartz hθ φ hφ x = phaseFun θ x * φ x := rfl


set_option maxHeartbeats 1000000 in
theorem solution {W θ : V → ℝ} (hW : Function.HasTemperateGrowth W)
    {m : V} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0)
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (schwartzDomain V) (opL2 (potMomOp W m)) z := by

  intro u hu
  have hmem : MemLp (fun x => (starRingEnd ℂ) (phaseFun θ x) * (u x)) 2
      (volume : Measure V) := by
    have hmeas : AEStronglyMeasurable (fun x => (starRingEnd ℂ) (phaseFun θ x) * (u x))
        (volume : Measure V) :=
      (Complex.continuous_conj.comp ((contDiff_phaseFun hθ).continuous)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u)
    refine (Lp.memLp u).of_le hmeas (Filter.Eventually.of_forall fun x => ?_)
    have hn : ‖phaseFun θ x‖ = 1 := norm_phaseFun' θ x
    simp [hn]
  set w : Lp ℂ 2 (volume : Measure V) := hmem.toLp _ with hwdef
  have hwcoe : ∀ᵐ x ∂(volume : Measure V),
      (w x : ℂ) = (starRingEnd ℂ) (phaseFun θ x) * (u x) := hmem.coeFn_toLp
  have hw : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) →
      ∫ x, (starRingEnd ℂ) ((momentumOp m φ) x) * (w x)
        = z * ∫ x, (starRingEnd ℂ) (φ x) * (w x) := by
    intro φ hφ
    have h1 := hu (schwartzEquiv V (phaseSchwartz hθ φ hφ))
    rw [opL2_apply, schwartzEquiv_coe, inner_toLp_left, inner_toLp_left] at h1
    have hL : ∫ x, (starRingEnd ℂ) ((momentumOp m φ) x) * (w x)
        = ∫ x, (starRingEnd ℂ) ((potMomOp W m (phaseSchwartz hθ φ hφ)) x) * (u x) := by
      refine integral_congr_ae ?_
      filter_upwards [hwcoe] with x hx
      rw [hx, potMomOp_gauge hW hθ hθd φ hφ x, map_mul]
      ring
    have hR : ∫ x, (starRingEnd ℂ) (φ x) * (w x)
        = ∫ x, (starRingEnd ℂ) ((phaseSchwartz hθ φ hφ) x) * (u x) := by
      refine integral_congr_ae ?_
      filter_upwards [hwcoe] with x hx
      rw [hx, phaseSchwartz_apply' hθ φ hφ, map_mul]
      ring
    rw [hL, hR, h1]
  have hw0 : w = 0 := momentumOp_eq_zero_of_compactSupport_test m hz w hw
  have hae : ∀ᵐ x ∂(volume : Measure V), (u x : ℂ) = 0 := by
    have h0 : ∀ᵐ x ∂(volume : Measure V), (w x : ℂ) = 0 := by
      rw [hw0]
      exact Lp.coeFn_zero ℂ 2 (volume : Measure V)
    filter_upwards [hwcoe, h0] with x hx hx0
    rw [hx] at hx0
    rcases mul_eq_zero.mp hx0 with h | h
    · have hn : ‖(starRingEnd ℂ) (phaseFun θ x)‖ = 1 := by
        rw [RCLike.norm_conj]
        exact norm_phaseFun' θ x
      rw [h, norm_zero] at hn
      exact absurd hn (by norm_num)
    · exact h
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hae
