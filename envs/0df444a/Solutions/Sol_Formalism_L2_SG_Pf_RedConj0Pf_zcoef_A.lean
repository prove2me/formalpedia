-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedConj0Pf.zcoef_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:00:30.071531+00:00
-- url     : https://prove2.me/submissions/ed1efea2-fb0c-48a6-a14a-40fb5dc8174e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ReductionConjugacy
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_ivH_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_mem_wLat0_of_iv
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_p_mem
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_zcoef
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
    (hz : ∑ l, z l • (Lw I w).mkQ (iv I (b l)) = 0) (l : Fin I.n) : ((z l : ℤ) : ZMod p) = 0 := by
  refine zcoef I w p hp hcard hb z ?_ l
  refine mem_wLat0_of_iv I w p hp.pos (p_mem I w p hp hcard) _ ?_
  have h : (Lw I w).mkQ (ivH I (∑ l, z l • b l)) = 0 := by
    rw [map_sum, map_sum]; simpa only [map_zsmul, ivH_apply] using hz
  exact (Submodule.Quotient.mk_eq_zero _).1 h
end Formalism.L2.SG.Pf.RedConj0Pf
