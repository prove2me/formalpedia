-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.rt0_conj_neg_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:36.888004+00:00
-- url     : https://prove2.me/submissions/3120f404-f846-47b6-82fa-4eece278e88f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEnc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PsiCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at h1 h2
  have hre : H.rt0.re = 0 := by
    rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im * 2 = 0 by linarith) with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact h
      · exfalso
        rw [h] at h1
        nlinarith [mul_self_nonneg H.rt0.re]
    · norm_num at h
  apply Complex.ext
  · simp [hre]
  · simp
end Formalism.MainNotions.ModuliIntegralCharts.H1
