-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.conj_LFunction_conj_of_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:42.008992+00:00
-- url     : https://prove2.me/submissions/fb35e274-ed05-4949-9b10-66407374c031

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TrivReal
import Theorems.Thm_Formalism_ZeroFreeDirichlet_conj_apply_of_sq_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    (z : ℂ) (hz : 1 < z.re) :
    starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z)) =
      DirichletCharacter.LFunction χ z := by
  have hz' : 1 < (starRingEnd ℂ z).re := by rwa [Complex.conj_re]
  rw [DirichletCharacter.LFunction_eq_LSeries χ hz', DirichletCharacter.LFunction_eq_LSeries χ hz,
    LSeries, LSeries, Complex.conj_tsum]
  congr 1
  funext m
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs with hm
  · exact map_zero _
  · show starRingEnd ℂ (χ m / (m : ℂ) ^ starRingEnd ℂ z) = χ m / (m : ℂ) ^ z
    have harg : (m : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    rw [map_div₀, conj_apply_of_sq_eq_one χ hχ, Complex.cpow_conj _ _ harg, map_natCast (starRingEnd ℂ) m,
      Complex.conj_conj]
end Formalism.ZeroFreeDirichlet
