-- Prove2me | solution 1 for Formalism.UG.P.wlocal_L_mul_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:58.956438+00:00
-- url     : https://prove2.me/submissions/b0383afc-d767-4aaa-99e0-03df4f52e5d4

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_L_mul_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]
namespace Formalism.UG.P
theorem _root_.solution {r : ℕ} (k : Fin r) (c d : Fin r → R) :
    wlocal_L k c * wlocal_L k d = wlocal_L k (c + d) := by
  ext i j
  rw [wlocal_L_mul_apply]
  simp only [wlocal_L, Pi.add_apply]
  by_cases hi : i = k
  · rw [hi]
    simp
  · by_cases hj : j = k
    · rw [hj]
      simp [hi] <;> ring
    · simp [hi, hj, Ne.symm hj]
end Formalism.UG.P
