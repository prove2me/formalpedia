-- Prove2me | solution 1 for Formalism.UG.P.UG_inclusion_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:56.517207+00:00
-- url     : https://prove2.me/submissions/c85abd99-1a62-48e5-bc27-8ea62f8ee396

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Theorems.Thm_Formalism_UG_P_bc_coe
import Theorems.Thm_Formalism_UG_P_inclE_injective

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
theorem _root_.solution : Formalism.UG.InclInj := by
  intro F E _ _ _ n _ _ R _ _ hR
  haveI := hR
  intro g g' hgg
  apply Units.ext
  have h1 := congrArg Units.val hgg
  rw [bc_coe, bc_coe] at h1
  ext i j
  exact inclE_injective F E R (congrFun (congrFun h1 i) j)
end Formalism.UG.P
