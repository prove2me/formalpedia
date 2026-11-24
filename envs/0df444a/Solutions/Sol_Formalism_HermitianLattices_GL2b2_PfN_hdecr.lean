-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2b2.PfN.hdecr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:52:06.954555+00:00
-- url     : https://prove2.me/submissions/17d77dc0-c69b-458c-a588-504780f1edff

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2b2
open Formalism.HermitianLattices.GL2b2.PfN
open Complex
namespace Formalism.HermitianLattices.GL2b2.PfN
theorem _root_.solution (σ x x' : ℝ) (hσ : 0 < σ) (hx : 0 < x) (hxx : x < x') :
    x' ^ (-σ) - (x' + 2) ^ (-σ) < x ^ (-σ) - (x + 2) ^ (-σ) := by
  have hx' : 0 < x' := hx.trans hxx
  have f : ∀ y : ℝ, 0 < y → (y + 2) ^ (-σ) = y ^ (-σ) * (1 + 2 / y) ^ (-σ) := by
    intro y hy
    rw [← Real.mul_rpow hy.le (by positivity)]
    congr 1
    field_simp
  rw [f x hx, f x' hx']
  have hA : x' ^ (-σ) < x ^ (-σ) := Real.rpow_lt_rpow_of_neg hx hxx (by linarith)
  have hA' : 0 < x' ^ (-σ) := Real.rpow_pos_of_pos hx' _
  have h2 : 2 / x' < 2 / x := div_lt_div_of_pos_left (by norm_num) hx hxx
  have hB : (1 + 2 / x) ^ (-σ) < (1 + 2 / x') ^ (-σ) :=
    Real.rpow_lt_rpow_of_neg (by positivity) (by linarith) (by linarith)
  have hB' : (1 + 2 / x') ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by have : 0 < 2 / x' := by positivity
                                          linarith) (by linarith)
  nlinarith [mul_pos hA' (sub_pos.2 hB'), mul_pos (sub_pos.2 hA) (sub_pos.2 (hB.trans hB')),
    mul_pos hA' (sub_pos.2 hB)]
end Formalism.HermitianLattices.GL2b2.PfN
