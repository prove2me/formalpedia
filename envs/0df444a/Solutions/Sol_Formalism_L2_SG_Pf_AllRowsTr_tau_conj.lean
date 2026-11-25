-- Prove2me | solution 1 for Formalism.L2.SG.Pf.AllRowsTr.tau_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:42.787447+00:00
-- url     : https://prove2.me/submissions/68cf6177-d018-438e-84be-bfd01fc51189

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsTr
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsTr_tau_mul_comm

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
theorem _root_.solution (P : G) (a : MonoidAlgebra ℂ G) :
    (MonoidAlgebra.single P 1 * a * MonoidAlgebra.single P⁻¹ 1).coeff 1 = a.coeff 1 := by
  rw [tau_mul_comm, ← mul_assoc, MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul,
    ← MonoidAlgebra.one_def, one_mul]
end Formalism.L2.SG.Pf.AllRowsTr
