-- Prove2me | solution 1 for Formalism.NG.congBoundGoodLarge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:17:49.589291+00:00
-- url     : https://prove2.me/submissions/b7420ed2-d572-448f-82b3-a45a9dba0f90

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_mem_Vx
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_cc_comm
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_cc_mem_VS
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_vcc_attain
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_congMod_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open QuotientPowerLengths
namespace Formalism.NG
theorem _root_.solution : StatCongBoundGoodLarge := by
  unfold StatCongBoundGoodLarge
  intro O _ _ _ X _ T _ _ V _ _ _ _ _ act hsum L hL _ hLT Z Zg _ _ a A haL hacomm hZgA hZ0
  have hVa : VS T act (Z : Set X) ≤ (VS T act (Zg : Set X)).comap a := by
    unfold VS
    refine iSup₂_le fun y hy => ?_
    intro v hv
    rw [Submodule.mem_comap]
    by_cases hyg : y ∈ Zg
    · rw [hZgA y hyg v hv]
      exact Submodule.smul_mem _ _
        ((le_iSup₂_of_le y (Finset.mem_coe.mpr hyg) le_rfl :
          Vx T act y ≤ ⨆ x ∈ (Zg : Set X), Vx T act x) hv)
    · rw [hZ0 y (Finset.mem_coe.mp hy) hyg v hv]
      exact Submodule.zero_mem _
  refine congMod_le hsum L hL Zg ((fun c : T => a * act c) '' (ccIdeal T (Z : Set X) : Set T))
    (fun x => vcc T (Z : Set X) x + addVal O (A : O)) ?_ ?_ ?_ ?_
  · rintro g ⟨c, -, rfl⟩ f
    show a * act c * act f = act f * (a * act c)
    rw [mul_assoc, cc_comm c f, ← mul_assoc, hacomm f, mul_assoc]
  · rintro g ⟨c, -, rfl⟩ v hv
    exact haL (act c v) (hLT c v hv)
  · rintro g ⟨c, hc, rfl⟩ v -
    exact hVa (cc_mem_VS hsum hc v)
  · intro x hx
    obtain ⟨c, hc, hcx⟩ := vcc_attain (T := T) (Z : Set X) x
    refine ⟨a * act c, ⟨c, hc, rfl⟩, (A : O) * (c : X → O) x, fun v hv => ?_, ?_⟩
    · show a (act c v) = _
      rw [(mem_Vx.mp hv) c, ← algebraMap_smul (FractionRing O) ((c : X → O) x) v, map_smul,
        hZgA x hx v hv, smul_smul,
        ← algebraMap_smul (FractionRing O) ((A : O) * (c : X → O) x) v, map_mul, map_intCast,
        mul_comm]
    · exact le_of_eq (by rw [addVal_mul, hcx, add_comm])
end Formalism.NG
