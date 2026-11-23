-- Prove2me | solution 1 for Formalism.UG.P.wlocal_L_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:24.848614+00:00
-- url     : https://prove2.me/submissions/8795f753-72a8-41f5-ba22-44e77bf9c9a4

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
theorem _root_.solution {r : ℕ} (k : Fin r) (c : Fin r → R) (M : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    (wlocal_L k c * M) i j = M i j + (if i ≠ k then c i * M k j else 0) := by
  by_cases h : i = k <;> simp [Matrix.mul_apply, wlocal_L, add_mul, Finset.sum_add_distrib, h]
end Formalism.UG.P
