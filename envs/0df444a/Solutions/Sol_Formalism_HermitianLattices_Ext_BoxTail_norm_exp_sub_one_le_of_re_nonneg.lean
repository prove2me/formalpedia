-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.norm_exp_sub_one_le_of_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:48.789092+00:00
-- url     : https://prove2.me/submissions/e9561442-5b3f-4d3b-8b80-2c285123402b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution (u : ℂ) (hu : 0 ≤ u.re) :
    ‖Complex.exp u - 1‖ ≤ Real.exp u.re * ‖u‖ := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => Complex.exp ((t : ℂ) * u)) (f' := fun t : ℝ => Complex.exp ((t : ℂ) * u) * u)
    (C := Real.exp u.re * ‖u‖) (a := 0) (b := 1)
    (fun t _ => by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * u) u t := by
        simpa using ((hasDerivAt_id t).ofReal_comp).mul_const u
      exact h1.cexp.hasDerivWithinAt)
    (fun t ht => by
      rw [norm_mul, Complex.norm_exp]
      have hre : ((t : ℂ) * u).re = t * u.re := by simp
      rw [hre]
      gcongr
      nlinarith [ht.1, ht.2])
    1 (by simp)
  simpa using key
end Formalism.HermitianLattices.Ext.BoxTail
