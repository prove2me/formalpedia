-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedConj0Pf.zcoef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:19:57.491798+00:00
-- url     : https://prove2.me/submissions/7b5c2768-08d8-413a-9ba7-7a0f45d8b649

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_wLat0_eq
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_int_mem_iff
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_span_of_red
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_indep
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
theorem _root_.solution (p : ℕ) (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {b : Fin I.n → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) (z : Fin I.n → ℤ)
    (hz : ∑ l, z l • b l ∈ wLat0 I w) (l : Fin I.n) : ((z l : ℤ) : ZMod p) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hsp := span_of_red I w hb
  have hc : ∑ j, (z j : 𝓞 I.E) • b j ∈ w.asIdeal • I.L := by
    rw [← wLat0_eq]
    convert hz using 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ext i; simp [Algebra.smul_def, zsmul_eq_mul]
  have h := indep I w hb.1 hsp (fun j => (z j : 𝓞 I.E)) hc l
  rw [int_mem_iff I w p hp hcard] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
end Formalism.L2.SG.Pf.RedConj0Pf
