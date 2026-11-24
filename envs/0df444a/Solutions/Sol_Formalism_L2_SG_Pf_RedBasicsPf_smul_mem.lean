-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:53:22.289055+00:00
-- url     : https://prove2.me/submissions/2112f746-a643-4b6f-95f9-96ba6212fb5c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_mem_wLat0_of_mem
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_iv_mem_w
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
theorem _root_.solution {a : 𝓞 I.E} (ha : a ∈ w.asIdeal) {u : Fin I.n → I.E ⊗[I.F] Af I.F} (hu : u ∈ I.Lf) :
    Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) • u ∈ lamAf (F := I.F) (wLat0 I w) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    have e : (Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) •
        fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((y : Fin I.n → I.E) i)) =
        iv I (((a : 𝓞 I.E) : I.E) • (y : Fin I.n → I.E)) := by
      funext i
      simp only [iv, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [e]
    exact iv_mem_w I w (mem_wLat0_of_mem I w ha y.2)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx
end Formalism.L2.SG.Pf.RedBasicsPf
