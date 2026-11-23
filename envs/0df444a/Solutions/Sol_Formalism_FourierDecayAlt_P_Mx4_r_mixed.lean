-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.r_mixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:43.353954+00:00
-- url     : https://prove2.me/submissions/c8e407d2-fc42-4c01-baa0-3526a6adef1b

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_up_fun
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_up_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_up_mixed1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_up_mixed2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_corner
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_sR_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_sR_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (P : Par) (hP : P.OK) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    (sR P l).transpose * sR P j = sR P j * (sR P l).transpose := by
  ext π2 π
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  by_cases h : ∃ π1, Up P j π π1 ∧ Up P l π2 π1
  · obtain ⟨π1, h1, h2⟩ := h
    obtain ⟨π3, h3, h4⟩ := up_mixed1 P l j hjl π π1 π2 h1 h2
    have L : ∑ b, sR P l b π2 * sR P j b π = sR P l π1 π2 * sR P j π1 π :=
      Finset.sum_eq_single π1 (fun b _ hb => by
        rw [sR_neg (l := j) (π := π) (π' := b) (fun hb' => hb (up_fun P j π b π1 hb' h1)), mul_zero])
        (fun h => absurd (Finset.mem_univ _) h)
    have R : ∑ b, sR P j π2 b * sR P l π b = sR P j π2 π3 * sR P l π π3 :=
      Finset.sum_eq_single π3 (fun b _ hb => by
        rw [sR_neg (l := l) (π := b) (π' := π) (fun hb' => hb (up_inj P l π b π3 hb' h3)), mul_zero])
        (fun h => absurd (Finset.mem_univ _) h)
    rw [L, R, sR_pos h1, sR_pos h2, sR_pos h3, sR_pos h4]
    exact (corner P hP l j hl hj hjl π3 π π2 h3 h4).2
  · have L : ∑ b, sR P l b π2 * sR P j b π = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      by_cases h1 : Up P j π b
      · rw [sR_neg (l := l) (π := π2) (π' := b) (fun h2 => h ⟨b, h1, h2⟩), zero_mul]
      · rw [sR_neg h1, mul_zero]
    have R : ∑ b, sR P j π2 b * sR P l π b = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      by_cases h1 : Up P l b π
      · rw [sR_neg (l := j) (π := b) (π' := π2) (fun h2 => h (up_mixed2 P l j hjl π π2 b h1 h2)), zero_mul]
      · rw [sR_neg h1, mul_zero]
    rw [L, R]
end Formalism.FourierDecayAlt.P.Mx4
