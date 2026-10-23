-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.norm_xCc_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:29:41.829084+00:00
-- url     : https://prove2.me/submissions/4bac45fe-bdd7-4177-814b-846aacdf6b50

-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.norm_xCc_sq_le
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterQgOuterFockFlow
open BookProof.ScalaronEsa
open BookProof.ScalaronFiberFL



open MeasureTheory SchwartzMap
open BookProof.StrichartzWave
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded BookProof.WallEsaBddBelow
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.SchrodingerCutoff BookProof.FriedrichsExtension

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (W : WallPot) (s : ℝ)
theorem sf83_int (f : ccSchwartz ℝ) {W : ℝ → ℝ} (hW : Continuous W) :
    Integrable fun x => W x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by
  have hf : HasCompactSupport (((f : 𝓢(ℝ, ℂ))) : ℝ → ℂ) := f.2
  have hc : HasCompactSupport (fun x => ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2) :=
    hf.norm.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  exact (hW.mul ((f : 𝓢(ℝ, ℂ)).continuous.norm.pow 2)).integrable_of_hasCompactSupport hc.mul_left

theorem solution (W : WallPot) (s : ℝ) (hs : 0 ≤ s) (f : ccSchwartz ℝ) :
    ‖xCc (ccEquiv ℝ f)‖ ^ 2 ≤ 4 * quadForm (W.ham s) (ccEquiv ℝ f) := by
  have hxe : xCc (ccEquiv ℝ f) = (mulCc (fun x : ℝ => x) contDiff_id f).toLp 2 := by
    simp [xCc, opCc]
  have hnorm : ‖xCc (ccEquiv ℝ f)‖ ^ 2 = ∫ x, x ^ 2 * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by
    rw [hxe, SchwartzMap.norm_toLp' two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    have hpt : ∀ x : ℝ, ‖(mulCc (fun x : ℝ => x) contDiff_id f) x‖ ^ (2:ℝ) =
        x ^ 2 * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by
      intro x
      change ‖((x : ℝ) : ℂ) * (f : 𝓢(ℝ, ℂ)) x‖ ^ (2:ℝ) = _
      rw [Real.rpow_two, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [hpt]
    rw [← one_div, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
    exact integral_nonneg fun x => by positivity
  have hint1 := sf83_int f (W := fun x : ℝ => x ^ 2) (continuous_pow 2)
  have hint2 := sf83_int f (W := fun x : ℝ => 4 * W.pot s x)
    (continuous_const.mul (W.pot_smooth s).continuous)
  have hmono : ∫ x, x ^ 2 * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 ≤
      ∫ x, (4 * W.pot s x) * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by
    refine integral_mono hint1 hint2 (fun x => mul_le_mul_of_nonneg_right ?_ (by positivity))
    have := W.nonneg x
    simp only [WallPot.pot]
    nlinarith
  have h4 : ∫ x, (4 * W.pot s x) * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 =
      4 * ∫ x, W.pot s x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have hd := integral_deriv_nonneg f
  rw [hnorm, ham_quadForm]
  linarith
