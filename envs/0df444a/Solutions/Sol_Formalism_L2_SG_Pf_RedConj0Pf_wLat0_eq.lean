-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedConj0Pf.wLat0_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:37:35.604995+00:00
-- url     : https://prove2.me/submissions/375e88da-817c-4b7d-8710-973317902f19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.L2.Host.restr_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField
open scoped TensorProduct Pointwise
open Matrix Formalism.MainNotions.S
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedConj0Pf
open Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
variable (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedConj0Pf
theorem _root_.solution : wLat0 I w = w.asIdeal • I.L := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, y, hy, rfl⟩
    have e : ((a : 𝓞 I.E) : I.E) • y = a • y := by first | rfl | (ext i; simp [Algebra.smul_def])
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem_smul ha hy
  · refine Submodule.smul_le.2 ?_
    intro a ha y hy
    have e : ((a : 𝓞 I.E) : I.E) • y = a • y := by first | rfl | (ext i; simp [Algebra.smul_def])
    exact Submodule.subset_span ⟨a, ha, y, hy, e.symm⟩
end Formalism.L2.SG.Pf.RedConj0Pf
