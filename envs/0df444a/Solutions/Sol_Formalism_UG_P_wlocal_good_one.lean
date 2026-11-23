-- Prove2me | solution 1 for Formalism.UG.P.wlocal_good_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:58.501811+00:00
-- url     : https://prove2.me/submissions/00a7615d-dad2-4642-9561-308842800564

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_rowAct_one

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
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    wlocal_Good hn ν (1 : Matrix (Fin r) (Fin r) R) := by
  intro f hf
  rw [wlocal_rowAct_one]
  exact hf
end Formalism.UG.P
