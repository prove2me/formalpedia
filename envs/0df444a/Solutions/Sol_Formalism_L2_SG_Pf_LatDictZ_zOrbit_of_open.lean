-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.zOrbit_of_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:30:08.290853+00:00
-- url     : https://prove2.me/submissions/dded4435-aec9-4dad-8172-2bdfbe41af37

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SemiGenusLocal
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_AlgebraMapNeZero
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_LocFin
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZOrbitOfOpen
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_semiGenusZ_of
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_LF_lattice_locally_finite
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGC_semi_genus_local
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_zOrbit_of
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_semiGenusZLoc_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ
namespace Formalism.L2.SG.Pf.LatDictZ
theorem _root_.solution (hP : Z0.PrimPlaneLoc) (hA : Z0.AdelGlue) : LatDictZ.ZOrbit :=
  Z0.zOrbit_of (Z0.BR.semiGenusZ_of (Z3.semiGenusZLoc_of Z0.SGC.semi_genus_local hP)) hA
    Z0.LF.lattice_locally_finite
end Formalism.L2.SG.Pf.LatDictZ
