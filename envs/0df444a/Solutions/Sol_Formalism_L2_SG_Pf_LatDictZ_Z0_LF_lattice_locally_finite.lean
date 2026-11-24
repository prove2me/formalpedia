-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.LF.lattice_locally_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:43:43.878809+00:00
-- url     : https://prove2.me/submissions/90ccfb74-ca02-44be-8d2f-788c21575714

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Lemmata_Denominators_Denom
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_LocFin
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_LF_lat_denom
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_LF_loc_le_of_denom
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.LF
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.LF
theorem _root_.solution : LocFinite := by
  intro E _ _ _ n L M hLfg hMfg hLsp hMsp
  obtain ⟨N₁, hN₁, h1⟩ := lat_denom L M hLfg hMsp
  obtain ⟨N₂, hN₂, h2⟩ := lat_denom M L hMfg hLsp
  have h0 : ((N₁ * N₂ : ℕ) : 𝓞 E) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (Nat.mul_pos hN₁ hN₂).ne'
  refine (Ring.HasFiniteQuotients.finite_setOfPred_mem _ h0).subset ?_
  rintro p ⟨hp, hne⟩
  by_contra hNp
  apply hne
  have hp' := hp.isPrime
  simp only [Set.mem_setOf_eq, Nat.cast_mul] at hNp
  have n1 : (N₁ : 𝓞 E) ∉ p := fun h => hNp (p.mul_mem_right _ h)
  have n2 : (N₂ : 𝓞 E) ∉ p := fun h => hNp (p.mul_mem_left _ h)
  exact le_antisymm (loc_le_of_denom h2 hp' n2) (loc_le_of_denom h1 hp' n1)
end Formalism.L2.SG.Pf.LatDictZ.Z0.LF
