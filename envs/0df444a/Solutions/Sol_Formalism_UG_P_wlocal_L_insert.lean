-- Prove2me | solution 1 for Formalism.UG.P.wlocal_L_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:58.057002+00:00
-- url     : https://prove2.me/submissions/fb333a29-dffe-4217-acfc-84903a55de61

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
theorem _root_.solution {r : ℕ} (k a : Fin r) (c : Fin r → R) (s : Finset (Fin r)) (ha : a ∉ s) (hak : a ≠ k) :
    wlocal_L k (fun i => if i ∈ insert a s then c i else 0) =
      wlocal_E a k (c a) * wlocal_L k (fun i => if i ∈ s then c i else 0) := by
  ext i j
  rw [wlocal_E_mul_apply]
  simp only [wlocal_L, Finset.mem_insert]
  by_cases hi : i = a
  · rw [hi]
    by_cases hj : j = k
    · rw [hj]
      simp [hak, ha]
    · simp [hak, ha, hj, Ne.symm hj]
  · simp [hi]
end Formalism.UG.P
