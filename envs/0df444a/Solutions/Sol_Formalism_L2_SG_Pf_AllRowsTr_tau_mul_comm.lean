-- Prove2me | solution 1 for Formalism.L2.SG.Pf.AllRowsTr.tau_mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:58:31.469119+00:00
-- url     : https://prove2.me/submissions/6da8348e-9d0d-4bd0-a43b-6b0b2d9311ac

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsTr
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_coeff_mul_fin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MonoidAlgebra
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.AllRowsTr
open Formalism.L2.SG.Pf.AllRowsGA
variable {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.SG.Pf.AllRowsTr
theorem _root_.solution (a b : MonoidAlgebra ℂ G) : (a * b).coeff 1 = (b * a).coeff 1 := by
  rw [coeff_mul_fin, coeff_mul_fin]
  simp only [mul_one]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun h => by rw [Equiv.inv_apply, inv_inv, mul_comm])
end Formalism.L2.SG.Pf.AllRowsTr
