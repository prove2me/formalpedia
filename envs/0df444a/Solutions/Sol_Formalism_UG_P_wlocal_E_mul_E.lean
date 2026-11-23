-- Prove2me | solution 1 for Formalism.UG.P.wlocal_E_mul_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:17.621502+00:00
-- url     : https://prove2.me/submissions/1d13f0d7-1422-4ef6-a9ce-a6379100a13f

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_E_mul_apply
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
theorem _root_.solution {r : ℕ} (a b : Fin r) (c d : R) :
    wlocal_E a b c * wlocal_E a b d = wlocal_E a b (c + d + (if a = b then c * d else 0)) := by
  ext i j
  rw [wlocal_E_mul_apply]
  simp only [wlocal_E]
  by_cases hi : i = a
  · rw [hi]
    by_cases hj : j = b
    · rw [hj]
      by_cases hab : a = b
      · rw [hab]
        simp <;> ring
      · simp [hab, Ne.symm hab] <;> ring
    · simp [hj, Ne.symm hj]
  · simp [hi]
end Formalism.UG.P
