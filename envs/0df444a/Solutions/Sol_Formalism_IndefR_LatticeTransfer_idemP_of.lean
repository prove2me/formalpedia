-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.idemP_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:56:17.816877+00:00
-- url     : https://prove2.me/submissions/056bbc92-79e7-4e5e-93da-3aed1d72f40c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_eS_comm
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_comm_epP
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_idem_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open IdempotentLemmas
namespace Formalism.IndefR.LatticeTransfer
theorem _root_.solution (h : CharFacts) : IdemP := by
  intro K _ _ G _ _ V _ _ _ _ ρ
  have hs' : ∀ (r : 𝓞 K) (v : V), ((r : K)) • v = r • v := fun r v => algebraMap_smul K r v
  have hcard : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨fun T _ _ _ τ => ⟨fun g => eS_comm τ ρ g,
    fun H χ => comm_epP ρ (eS τ ρ) (fun g => eS_comm τ ρ g) H χ, fun A hA a ha => ?_⟩,
    fun H χ => ⟨?_, fun A hA a ha => ?_⟩⟩
  · have hint : ∀ x : G, IsIntegral ℤ (charOf τ 1 * charOf τ x⁻¹) :=
      fun x => (h K G T τ 1).1.mul (h K G T τ x⁻¹).1
    have hd : (Fintype.card G : K) * (charOf τ 1 / (Fintype.card G : K)) = charOf τ 1 := by
      field_simp
    rw [← hs', show ((Fintype.card G : 𝓞 K) : K) = (Fintype.card G : K) by simp, eS,
      LinearMap.smul_apply, smul_smul, hd, LinearMap.sum_apply, Finset.smul_sum]
    refine A.sum_mem fun x _ => ?_
    rw [LinearMap.smul_apply, smul_smul]
    have hx : charOf τ 1 * charOf τ x⁻¹ ∈ integralClosure ℤ K := hint x
    let r : 𝓞 K := ⟨_, hx⟩
    have hm := A.smul_mem r (hA x a ha)
    have he : (charOf τ 1 * charOf τ x⁻¹) • ρ x a = r • ρ x a := hs' r (ρ x a)
    rw [he]
    exact hm
  · have hn : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    show epP H χ ρ * epP H χ ρ = epP H χ ρ
    unfold epP
    exact idem_gen (fun h : H => (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K))
      (fun h k => by simp only [mul_inv_rev, map_mul, Units.val_mul]; ring)
      (ρ.comp H.subtype) hn
  · have hn : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hI : ((Fintype.card G : 𝓞 K) : K) * (Nat.card H : K)⁻¹ = ((H.index : 𝓞 K) : K) := by
      have hG : (Fintype.card G : K) = (Nat.card H : K) * H.index := by
        rw [← Nat.card_eq_fintype_card, ← H.card_mul_index, Nat.cast_mul]
      simp only [map_natCast]
      rw [hG]
      field_simp
    rw [← hs']
    unfold epP
    rw [LinearMap.smul_apply, smul_smul, hI, hs', LinearMap.sum_apply]
    refine A.smul_mem _ (A.sum_mem fun h _ => ?_)
    rw [LinearMap.smul_apply, hs']
    exact A.smul_mem _ (hA _ _ ha)
end Formalism.IndefR.LatticeTransfer
