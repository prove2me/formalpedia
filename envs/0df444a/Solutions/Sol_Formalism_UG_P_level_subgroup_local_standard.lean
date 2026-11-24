-- Prove2me | solution 1 for Formalism.UG.P.level_subgroup_local_standard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:05:26.565857+00:00
-- url     : https://prove2.me/submissions/1b2a34ed-6c73-4117-a43e-199c5ec759ed

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
import Theorems.Thm_Formalism_UG_P_easyc_latS_std

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.LevelVLStd := by
  intro F E _ _ _ _ _ n _ _ σ J v
  unfold levelVL levelV
  rw [easyc_latS_std]
end Formalism.UG.P
