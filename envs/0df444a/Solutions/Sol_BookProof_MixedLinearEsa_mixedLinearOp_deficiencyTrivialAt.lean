-- Prove2me | solution 1 for BookProof.MixedLinearEsa.mixedLinearOp_deficiencyTrivialAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T07:03:09.607163+00:00
-- url     : https://prove2.me/submissions/a32b25de-ae26-434e-b2ed-6564f8e6307a

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.mixedLinearOp_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Theorems.Thm_BookProof_MixedLinearEsa_posOp_deficiencyTrivialAt
import Theorems.Thm_BookProof_MixedLinearEsa_momentumOp_apply
import Theorems.Thm_BookProof_MixedLinearEsa_momentumOp_eq_zero_of_compactSupport_test
import Theorems.Thm_BookProof_MixedLinearEsa_norm_gaugeFun
import Theorems.Thm_BookProof_MixedLinearEsa_mixedLinearOp_gauge
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_StrichartzWave_schwartzEquiv_coe
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.MixedLinearEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine
open BookProof.FourierMultiplierEsa
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! `gaugeSchwartz_apply` exists in the source chapter but no
`Theorems/Thm_…` stub was generated for it, so a solution may not import it.  It
is a definitional `rfl` over `gaugeSchwartz`/`gaugeFun`, both of which the
platform publishes, so it is stated locally as `private`.
-/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem gaugeSchwartz_apply' (b m : V) (φ : 𝓢(V, ℂ))
    (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) :
    gaugeSchwartz b m φ hφ x = gaugeFun b m x * φ x := rfl

set_option maxHeartbeats 1000000 in
theorem solution (b m : V) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (schwartzDomain V) (opL2 (mixedLinearOp b m)) z := by

  rcases eq_or_ne m 0 with rfl | hm
  · have h0 : mixedLinearOp b (0 : V) = posOp b := by
      have h : momentumOp (0 : V) = 0 := by
        ext f x
        simp [momentumOp_apply]
      rw [mixedLinearOp, h, add_zero]
    rw [h0]
    exact posOp_deficiencyTrivialAt b hz
  intro u hu
  have hmem : MemLp (fun x => (starRingEnd ℂ) (gaugeFun b m x) * (u x)) 2
      (volume : Measure V) := by
    have hmeas : AEStronglyMeasurable (fun x => (starRingEnd ℂ) (gaugeFun b m x) * (u x))
        (volume : Measure V) :=
      (Complex.continuous_conj.comp ((contDiff_gaugeFun b m).continuous)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u)
    refine (Lp.memLp u).of_le hmeas (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_gaugeFun]
  set w : Lp ℂ 2 (volume : Measure V) := hmem.toLp _ with hwdef
  have hwcoe : ∀ᵐ x ∂(volume : Measure V),
      (w x : ℂ) = (starRingEnd ℂ) (gaugeFun b m x) * (u x) := hmem.coeFn_toLp
  have hw : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) →
      ∫ x, (starRingEnd ℂ) ((momentumOp m φ) x) * (w x)
        = z * ∫ x, (starRingEnd ℂ) (φ x) * (w x) := by
    intro φ hφ
    have h1 := hu (schwartzEquiv V (gaugeSchwartz b m φ hφ))
    rw [opL2_apply, schwartzEquiv_coe, inner_toLp_left, inner_toLp_left] at h1
    have hL : ∫ x, (starRingEnd ℂ) ((momentumOp m φ) x) * (w x)
        = ∫ x, (starRingEnd ℂ) ((mixedLinearOp b m (gaugeSchwartz b m φ hφ)) x) * (u x) := by
      refine integral_congr_ae ?_
      filter_upwards [hwcoe] with x hx
      rw [hx, mixedLinearOp_gauge b m hm φ hφ x, map_mul]
      ring
    have hR : ∫ x, (starRingEnd ℂ) (φ x) * (w x)
        = ∫ x, (starRingEnd ℂ) ((gaugeSchwartz b m φ hφ) x) * (u x) := by
      refine integral_congr_ae ?_
      filter_upwards [hwcoe] with x hx
      rw [hx, gaugeSchwartz_apply', map_mul]
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
    · have hn : ‖(starRingEnd ℂ) (gaugeFun b m x)‖ = 1 := by
        rw [RCLike.norm_conj]
        exact norm_gaugeFun b m x
      rw [h, norm_zero] at hn
      exact absurd hn (by norm_num)
    · exact h
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hae
