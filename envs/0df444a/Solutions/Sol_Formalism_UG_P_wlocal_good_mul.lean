-- Prove2me | solution 1 for Formalism.UG.P.wlocal_good_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:58.41826+00:00
-- url     : https://prove2.me/submissions/2e121269-4abf-41bc-a42f-b1e75dc4de4e

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_rowAct_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]
namespace Formalism.UG.P
theorem _root_.solution {r n : ℕ} {hn : n ≤ r} {ν : Fin n → ℕ} {A B : Matrix (Fin r) (Fin r) R}
    (hA : wlocal_Good hn ν A) (hB : wlocal_Good hn ν B) : wlocal_Good hn ν (A * B) := by
  intro f hf
  rw [wlocal_rowAct_mul, AlgHom.comp_apply]
  exact hB _ (hA f hf)
end Formalism.UG.P
