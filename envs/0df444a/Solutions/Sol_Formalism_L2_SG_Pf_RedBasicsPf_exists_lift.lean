-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:48:57.704716+00:00
-- url     : https://prove2.me/submissions/09b4c1c3-f90c-4bfd-aa84-0fe1c9b3040d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_RedBasicsPf_mk_sum__ba6933ed2daa
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
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedBasicsPf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
attribute [local instance] Ideal.Quotient.field
variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedBasicsPf
theorem _root_.solution (y : I.L) {d : ℕ} (e : Module.Basis (Fin d) (𝓞 I.E ⧸ w.asIdeal) (RedQ I w))
    (b' : Fin d → I.L) (hb' : ∀ i, Submodule.Quotient.mk (b' i) = e i) :
    ∃ α : Fin d → 𝓞 I.E, y - ∑ i, α i • b' i ∈ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)) := by
  have hκ : ∀ i, ∃ a : 𝓞 I.E, Ideal.Quotient.mk w.asIdeal a = e.repr (Submodule.Quotient.mk y) i :=
    fun i => Ideal.Quotient.mk_surjective _
  choose α hα using hκ
  refine ⟨α, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, mk_sum']
  simp only [← Module.Quotient.mk_smul_mk, hα, hb']
  rw [e.sum_repr, sub_self]
end Formalism.L2.SG.Pf.RedBasicsPf
