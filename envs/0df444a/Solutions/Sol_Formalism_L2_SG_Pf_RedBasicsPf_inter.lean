-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:50:04.369318+00:00
-- url     : https://prove2.me/submissions/a06b5003-f66a-4e56-9abb-32fc9b5739b6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_coe_smul
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_wLat0_le
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_smul_mem_wLat0
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_mem_wLat0_of_mem
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_lamAf_w_le
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_lamAf_mono
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_smul_mem
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_exists_ideal_element_not_mem
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_P2M_PIW_AdelClassFin_lattice_intersection__c78dcf3d0364
import Theorems.Thm_PIW_AdelClassFin_DictGen_iv_mem
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
theorem _root_.solution {v : Fin I.n → I.E} (hv : iv I v ∈ lamAf (F := I.F) (wLat0 I w)) : v ∈ wLat0 I w := by
  have hvL : v ∈ I.L := lattice_intersection' I v (lamAf_mono I (wLat0_le I w) hv)
  obtain ⟨t, β, htw, ht0, hβ, hβw⟩ := exists_ideal_element_not_mem I w
  let φβ : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₗ[IntAf I.F I.E] (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    ((Formalism.UG.inclE (F := I.F) (Af I.F) ((β : 𝓞 I.E) : I.E)) • (LinearMap.id : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₗ[I.E ⊗[I.F] Af I.F] _)).restrictScalars _
  let φt : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₗ[IntAf I.F I.E] (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    ((Formalism.UG.inclE (F := I.F) (Af I.F) ((t : 𝓞 I.E) : I.E)) • (LinearMap.id : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₗ[I.E ⊗[I.F] Af I.F] _)).restrictScalars _
  have hle : lamAf (F := I.F) (wLat0 I w) ≤ (I.Lf.map φt).comap φβ := by
    refine lamAf_w_le I w _ (fun a ha y hy => ?_)
    obtain ⟨g, hg⟩ := hβ a ha
    rw [Submodule.mem_comap, Submodule.mem_map]
    refine ⟨iv I (((g : 𝓞 I.E) : I.E) • y),
      DictLat.iv_mem I (by rw [coe_smul]; exact I.L.smul_mem g hy), ?_⟩
    show Formalism.UG.inclE (F := I.F) (Af I.F) ((t : 𝓞 I.E) : I.E) • iv I (((g : 𝓞 I.E) : I.E) • y) =
      Formalism.UG.inclE (F := I.F) (Af I.F) ((β : 𝓞 I.E) : I.E) • iv I (((a : 𝓞 I.E) : I.E) • y)
    rw [DictLat.iv_smulE, DictLat.iv_smulE, smul_smul, smul_smul]
    congr 1
    simp only [← map_mul, hg]
  obtain ⟨u, hu, hue⟩ := (Submodule.mem_map).1 (hle hv)
  have hue' : Formalism.UG.inclE (F := I.F) (Af I.F) ((t : 𝓞 I.E) : I.E) • u = Formalism.UG.inclE (F := I.F) (Af I.F) ((β : 𝓞 I.E) : I.E) • iv I v := hue
  have htE : ((t : 𝓞 I.E) : I.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ht0
  have hz : iv I (((t : 𝓞 I.E) : I.E)⁻¹ • ((β : 𝓞 I.E) : I.E) • v) = u := by
    rw [DictLat.iv_smulE, DictLat.iv_smulE, ← hue', smul_smul, ← map_mul, inv_mul_cancel₀ htE, map_one,
      one_smul]
  have hzL : ((t : 𝓞 I.E) : I.E)⁻¹ • ((β : 𝓞 I.E) : I.E) • v ∈ I.L :=
    lattice_intersection' I _ (by rw [hz]; exact hu)
  have hβv : ((β : 𝓞 I.E) : I.E) • v ∈ wLat0 I w := by
    have e1 : ((β : 𝓞 I.E) : I.E) • v =
        ((t : 𝓞 I.E) : I.E) • (((t : 𝓞 I.E) : I.E)⁻¹ • ((β : 𝓞 I.E) : I.E) • v) := by
      rw [smul_smul, mul_inv_cancel₀ htE, one_smul]
    rw [e1]
    exact mem_wLat0_of_mem I w htw hzL
  obtain ⟨γ, i, hi, hγ⟩ := Ideal.IsMaximal.exists_inv (inferInstance : w.asIdeal.IsMaximal) hβw
  have hγ' : ((γ : 𝓞 I.E) : I.E) * ((β : 𝓞 I.E) : I.E) + ((i : 𝓞 I.E) : I.E) = 1 := by
    have := congrArg (fun z : 𝓞 I.E => (z : I.E)) hγ
    simpa using this
  have e2 : v = ((γ : 𝓞 I.E) : I.E) • (((β : 𝓞 I.E) : I.E) • v) + ((i : 𝓞 I.E) : I.E) • v := by
    rw [smul_smul, ← add_smul, hγ', one_smul]
  rw [e2]
  exact Submodule.add_mem _ (smul_mem_wLat0 I w γ hβv) (mem_wLat0_of_mem I w hi hvL)
end Formalism.L2.SG.Pf.RedBasicsPf
