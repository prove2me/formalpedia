-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.wLat0_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:00.840885+00:00
-- url     : https://prove2.me/submissions/8cfa4b33-db05-45b8-be14-9e7f96b133cc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_coe_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedBasicsPf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
attribute [local instance] Ideal.Quotient.field
variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedBasicsPf
theorem _root_.solution : wLat0 I w = w.asIdeal • I.L := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro z ⟨a, ha, y, hy, rfl⟩
    rw [coe_smul]
    exact Submodule.smul_mem_smul ha hy
  · refine Submodule.smul_le.mpr fun r hr n hn => ?_
    rw [← coe_smul]
    exact Submodule.subset_span ⟨r, hr, n, hn, rfl⟩
end Formalism.L2.SG.Pf.RedBasicsPf
