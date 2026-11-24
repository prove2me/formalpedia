-- Prove2me | solution 1 for Formalism.UG.P.wlocal_L_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:57.058038+00:00
-- url     : https://prove2.me/submissions/9b9b3a20-b6c2-4b0e-b5d5-8d50efbbc3a5

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
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
theorem _root_.solution {r : ℕ} (k : Fin r) (c d : Fin r → R) (h : ∀ i, i ≠ k → c i = d i) :
    wlocal_L k c = wlocal_L k d := by
  ext i j
  simp only [wlocal_L]
  by_cases hi : i = k
  · simp [hi]
  · rw [h i hi]
end Formalism.UG.P
