-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.val_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:10:29.573825+00:00
-- url     : https://prove2.me/submissions/c6f3bab5-5f58-4051-8b22-943767e5d4f2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_mem_wLat0_of_mem
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_natCast_mem
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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {z : Fin I.n → I.E} (hz : z ∈ I.L) (c : ℤ) :
    ((((c : ZMod p)).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I z - (c : I.E ⊗[I.F] Af I.F) • iv I z ∈
      lamAf (F := I.F) (wLat0 I w) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hd : (p : ℤ) ∣ ((c : ZMod p).val : ℤ) - c := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp
  obtain ⟨k, hk⟩ := hd
  have hm : (p : 𝓞 I.E) * (k : 𝓞 I.E) ∈ w.asIdeal := Ideal.mul_mem_right _ _ (natCast_mem I w hp hcard)
  have h1 := iv_mem_w I w (mem_wLat0_of_mem I w hm hz)
  have e : ((((c : ZMod p)).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I z - (c : I.E ⊗[I.F] Af I.F) • iv I z =
      iv I ((((p : 𝓞 I.E) * (k : 𝓞 I.E) : 𝓞 I.E) : I.E) • z) := by
    funext i
    have hk' : ((((c : ZMod p).val : ℤ) - c : ℤ) : I.E ⊗[I.F] Af I.F) = ((p * k : ℤ) : I.E ⊗[I.F] Af I.F) := by
      rw [hk]
    push_cast at hk'
    simp only [iv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [← sub_mul, hk', map_mul, map_mul, map_natCast]
    simp
  rw [e]
  exact h1
end Formalism.L2.SG.Pf.RedBasicsPf
