-- Prove2me | solution 1 for Formalism.BasicNotions.Host.MuCond.even_im_hermitian_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:33:40.436839+00:00
-- url     : https://prove2.me/submissions/281ce27d-57fa-4ee8-b648-973f042bffe8

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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


section
open NumberField Formalism.FrobeniusOrbits Formalism.HC
namespace Formalism.BasicNotions
section cls
variable {φ : Frame} (H : HostRaw φ) {p : ℕ}
variable {H}
end cls
namespace Ranks
variable (R : Ranks)
end Ranks
namespace Host
variable {R : Ranks} (H : Host R)
private theorem sum_even_of_prod_neg_one_zpow_eq_one {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι]
    (k : ι → ℤ) (h : ∏ τ, (-1 : K) ^ k τ = 1) : ∃ z : ℤ, ∑ τ, k τ = 2 * z := by
  have key : ∀ τ, (-1 : K) ^ k τ = (((-1 : Kˣ) ^ k τ : Kˣ) : K) := fun τ => by
    rw [Units.val_zpow_eq_zpow_val, Units.val_neg, Units.val_one]
  have hsum : ∀ s : Finset ι, ∏ τ ∈ s, (-1 : Kˣ) ^ k τ = (-1 : Kˣ) ^ (∑ τ ∈ s, k τ) := by
    classical
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  rw [Finset.prod_congr rfl (fun τ _ => key τ), ← Units.coe_prod, hsum] at h
  rcases Int.even_or_odd (∑ τ, k τ) with ⟨w, hw⟩ | hodd
  · exact ⟨w, by rw [hw]; ring⟩
  · exfalso
    rw [hodd.neg_one_zpow, Units.val_neg, Units.val_one] at h
    have h4 : (2 : K) = 0 := by linear_combination -h
    norm_num at h4
end Host
end Formalism.BasicNotions
end

set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.HC
open Formalism Formalism.BasicNotions
open Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
variable {H}
namespace Formalism.BasicNotions.Host
namespace MuCond
theorem _root_.solution {ι : Type} [Fintype ι] {g : ι → R.GG} {e : ι → ℚ} (h : H.MuCond g e) (he : ∀ τ, ∃ z : ℤ, e τ = z) :
    ∃ z : ℤ, ∑ τ, e τ = 2 * z := by
  have h1 := h (-1) ⟨2, by norm_num, by norm_num⟩
  simp only [map_neg, map_one] at h1
  obtain ⟨w, hw⟩ := sum_even_of_prod_neg_one_zpow_eq_one (fun τ => (e τ).num) h1
  refine ⟨w, ?_⟩
  have hnum : ∀ τ, (((e τ).num : ℤ) : ℚ) = e τ := fun τ => by
    obtain ⟨z, hz⟩ := he τ
    rw [hz]
    simp
  have h3 : ((∑ τ, (e τ).num : ℤ) : ℚ) = ((2 * w : ℤ) : ℚ) := by exact_mod_cast hw
  push_cast at h3
  simp only [hnum] at h3
  exact h3
end MuCond
end Formalism.BasicNotions.Host
