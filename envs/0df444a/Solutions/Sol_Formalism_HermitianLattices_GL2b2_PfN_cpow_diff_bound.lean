-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2b2.PfN.cpow_diff_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:08:04.022657+00:00
-- url     : https://prove2.me/submissions/7b1ded6d-26a9-4a13-9961-6511a96ce228

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2b2
open Formalism.HermitianLattices.GL2b2.PfN
open Complex
namespace Formalism.HermitianLattices.GL2b2.PfN
theorem _root_.solution (s : ℂ) (hs : 0 ≤ s.re) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    ‖((y : ℝ) : ℂ) ^ (-s) - ((x : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * x ^ (-s.re - 1) * (y - x) := by
  have hder : ∀ t ∈ Set.Icc x y, HasDerivWithinAt (fun u : ℝ => ((u : ℝ) : ℂ) ^ (-s))
      ((-s) * ((t : ℝ) : ℂ) ^ (-s - 1)) (Set.Icc x y) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hx ht.1
    have h1 : HasDerivAt (fun z : ℂ => z ^ (-s)) ((-s) * ((t : ℝ) : ℂ) ^ (-s - 1)) ((t : ℝ) : ℂ) := by
      have := (hasDerivAt_id ((t : ℝ) : ℂ)).cpow_const (c := -s) (Complex.ofReal_mem_slitPlane.2 ht0)
      simpa using this
    exact h1.comp_ofReal.hasDerivWithinAt
  have hb : ∀ t ∈ Set.Icc x y, ‖(-s) * ((t : ℝ) : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hx ht.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have : (-s - 1).re = -s.re - 1 := by simp
    rw [this]
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 ht0) ht.1
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb (convex_Icc x y)
    (Set.left_mem_Icc.2 hxy) (Set.right_mem_Icc.2 hxy)
  rwa [Real.norm_of_nonneg (by linarith)] at this
end Formalism.HermitianLattices.GL2b2.PfN
