-- Prove2me | solution 1 for Formalism.UG.P.base_change_mem_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:13.133409+00:00
-- url     : https://prove2.me/submissions/81c1ad21-0270-4865-a155-d51b47f7efb7

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Theorems.Thm_Formalism_UG_P_cT_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.BCMem := by
  intro A B _ _ n _ _ σ σ' φ h J g hg
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((bc φ g : GL n B) : Matrix n n B) * J.map φ * ((bc φ g : GL n B) : Matrix n n B) =
    J.map φ
  have e : ((bc φ g : GL n B) : Matrix n n B) = (g : Matrix n n A).map φ := rfl
  rw [e, cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']
end Formalism.UG.P
