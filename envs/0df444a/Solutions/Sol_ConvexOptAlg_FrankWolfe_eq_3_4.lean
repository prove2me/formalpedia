-- Prove2me | solution 1 for ConvexOptAlg.FrankWolfe.eq_3_4
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:44:23.314847+00:00
-- url     : https://prove2.me/submissions/63439c16-7abe-4ff1-a84e-87948472bbf1

import Definitions.Def_ConvexOptAlg_FrankWolfe_Defs

open ConvexOptAlg.FrankWolfe
open Set

set_option maxHeartbeats 800000

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (hXconv : Convex ℝ X)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothNormOn X f f' β)
    (x y : E) (hx : x ∈ X) (hy : y ∈ X) :
    0 ≤ f x - f y - f' y (x - y) ∧ f x - f y - f' y (x - y) ≤ β / 2 * ‖x - y‖ ^ 2 := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => f (AffineMap.lineMap y x t))
      (f' (AffineMap.lineMap y x t) (x - y)) t :=
    (hsmooth.1 _).comp_hasDerivAt t AffineMap.hasDerivAt_lineMap
  have hc := ConvexOn.comp_affineMap (AffineMap.lineMap y x) hf
  have hlo := hc.le_slope_of_hasDerivAt (x := (0 : ℝ)) (y := 1)
    (by simpa using hy) (by simpa using hx) zero_lt_one (hd 0)
  simp only [Function.comp_apply, slope_def_field, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at hlo
  refine ⟨by linarith, ?_⟩
  let q : ℝ → ℝ := fun t => f (AffineMap.lineMap y x t) - f y -
    t * f' y (x - y) - β / 2 * t ^ 2 * ‖x - y‖ ^ 2
  have hq (t : ℝ) : HasDerivAt q
      (f' (AffineMap.lineMap y x t) (x - y) - f' y (x - y) -
        β * t * ‖x - y‖ ^ 2) t := by
    have hquad := (((hasDerivAt_id t).pow 2).const_mul (β / 2)).mul_const (‖x - y‖ ^ 2)
    convert (((hd t).sub_const (f y)).sub
      ((hasDerivAt_id t).mul_const (f' y (x - y)))).sub hquad using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hanti : AntitoneOn q (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t _ => (hq t).continuousAt.continuousWithinAt)
      (fun t _ => (hq t).hasDerivWithinAt)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    have hz : AffineMap.lineMap y x t ∈ X := by
      rw [AffineMap.lineMap_apply_module]
      exact hXconv hy hx (sub_nonneg.mpr ht'.2) ht'.1 (by ring)
    have hn := hsmooth.2 _ hz y hy
    have he := (f' (AffineMap.lineMap y x t) - f' y).le_opNorm (x - y)
    have hbound : f' (AffineMap.lineMap y x t) (x - y) - f' y (x - y) ≤
        β * t * ‖x - y‖ ^ 2 := by
      calc
        _ ≤ ‖(f' (AffineMap.lineMap y x t) - f' y) (x - y)‖ := by
          simpa only [sub_apply, Real.norm_eq_abs] using
            (le_abs_self (f' (AffineMap.lineMap y x t) (x - y) - f' y (x - y)))
        _ ≤ ‖f' (AffineMap.lineMap y x t) - f' y‖ * ‖x - y‖ := he
        _ ≤ (β * ‖AffineMap.lineMap y x t - y‖) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg _)
        _ = β * t * ‖x - y‖ ^ 2 := by
          rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, norm_smul,
            Real.norm_eq_abs, abs_of_nonneg ht'.1]
          ring
    linarith
  have h01 := hanti (by simp) (by simp) (show (0 : ℝ) ≤ 1 by norm_num)
  dsimp [q] at h01
  simp only [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero,
    zero_mul, one_mul, zero_pow (by decide : 2 ≠ 0), one_pow,
    mul_zero, mul_one, sub_self] at h01
  linarith
