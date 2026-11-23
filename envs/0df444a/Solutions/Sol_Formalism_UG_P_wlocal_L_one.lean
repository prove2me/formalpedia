-- Prove2me | solution 1 for Formalism.UG.P.wlocal_L_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:24.798927+00:00
-- url     : https://prove2.me/submissions/2c66f67b-4bf7-4ec6-a8a9-3a242b6d139e

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
theorem _root_.solution {r : ℕ} (k : Fin r) : wlocal_L k (0 : Fin r → R) = 1 := by
  ext i j
  simp [wlocal_L, Matrix.one_apply]
end Formalism.UG.P
