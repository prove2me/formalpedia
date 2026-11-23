-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.omega_norm_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:33.975434+00:00
-- url     : https://prove2.me/submissions/ce89953b-e3e3-48a6-93df-7def77865db8

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Real
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.OmNorm := by
  intro V _ _ ip hadd hsmul hconj z x T T' Dr hT hzz hxx
  have hadd2 : ∀ w x y, ip w (x + y) = ip w x + ip w y := by
    intro w x y
    rw [hconj (x + y) w, hadd, map_add, ← hconj, ← hconj]
  have hsmul2 : ∀ (s : ℂ) w y, ip w (s • y) = starRingEnd ℂ s * ip w y := by
    intro s w y
    rw [hconj (s • y) w, hsmul, map_mul, ← hconj]
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  set ζ := ip x z with hζ
  have hzx : ip z x = starRingEnd ℂ ζ := hconj x z
  constructor
  · rw [hsmul, hadd, hsmul, hzz]
    field_simp
    ring
  · rw [hsmul, hsmul2, hadd, hadd2, hadd2, hsmul, hsmul, hsmul2, hsmul2, hxx, hzz, hzx, ← hζ]
    apply Complex.ext
    · simp [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
      field_simp
      ring
    · simp [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
      field_simp
      ring
end Formalism.FourierDecayAlt.P
