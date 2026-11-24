-- Prove2me | solution 1 for Formalism.L2.Th1.A.ISer.eq_wSer_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:20:15.030005+00:00
-- url     : https://prove2.me/submissions/71d616f5-c3b0-460b-a0a2-d23643a330c8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_apply
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_X
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_C
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.ISer
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A.ISer
theorem _root_.solution (hW : WSerSpec.{u}) (W : WeierstrassCurve R) (s v : R⟦X⟧)
    (hs : constantCoeff s = 0) (hv : constantCoeff v = 0)
    (h : v = s ^ 3 + C W.a₁ * s * v + C W.a₂ * s ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * s * v ^ 2
      + C W.a₆ * v ^ 3) : v = (wSer W).subst s := by
  set w := (wSer W).subst s with hw
  obtain ⟨hfix0, hfix⟩ := (hW R W).1
  have hweq : w = s ^ 3 + C W.a₁ * s * w + C W.a₂ * s ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * s * w ^ 2
      + C W.a₆ * w ^ 3 := by
    have h2 := congrArg (subHom s hs) hfix
    simp only [map_add, map_mul, map_pow, subHom_X, subHom_C] at h2
    rw [subHom_apply] at h2
    exact h2
  have hw0 : constantCoeff w = 0 := by
    obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hfix0
    have h3 : w = s * subHom s hs q := by
      rw [hw, ← subHom_apply s hs, hq, map_mul, subHom_X]
    rw [h3, map_mul, hs, zero_mul]
  set E := C W.a₁ * s + C W.a₂ * s ^ 2 + C W.a₃ * (v + w) + C W.a₄ * s * (v + w)
    + C W.a₆ * (v ^ 2 + v * w + w ^ 2) with hE
  have h4 : v - w = (v - w) * E := by
    rw [hE]
    linear_combination h - hweq
  have hd : (v - w) * (1 - E) = 0 := by linear_combination h4
  have hu : IsUnit (1 - E) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have h5 : constantCoeff E = 0 := by
      rw [hE]
      simp [hs, hv, hw0]
    rw [map_sub, map_one, h5, sub_zero]
    exact isUnit_one
  exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp hd)
end Formalism.L2.Th1.A.ISer
