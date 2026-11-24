-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.lseries_zetaMul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:44:07.8507+00:00
-- url     : https://prove2.me/submissions/405cb72c-2e12-4baa-a66d-73a10b9cd520

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ConvolutionNonnegOfDivisors
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqCoeff
import Theorems.Thm_Formalism_ZeroFreeDirichlet_dirichlet_character_lseries_summable
import Theorems.Thm_Formalism_ZeroFreeDirichlet_dirichlet_character_lseries_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction
open scoped ComplexOrder LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
set_option backward.isDefEq.respectTransparency.types false
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (DirichletCharacter.zetaMul χ) s = riemannZeta s * DirichletCharacter.LFunction χ s := by
  have h1 : LSeriesSummable ⇑(ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    have := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
    exact (LSeriesSummable_congr s (fun {n} hn => by simp [hn])).mp this
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.LSeries_mul' h1 (dirichlet_character_lseries_summable χ hs),
    dirichlet_character_lseries_eq χ hs]
  congr 1
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact LSeries_congr (fun {n} hn => by simp [hn]) s
end Formalism.ZeroFreeDirichlet
